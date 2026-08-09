/-
# Theory.CredentialAuthorityEffects -- canonical authority mutations

Issuance, strict attenuation, revocation, and epoch rotation are ordinary
`AcceptedCellEffect` families over `CredentialAuthorityState.schema`.  Each
family writes one exact authority cell together with one exact single-use
nullifier cell in the same validated patch.  No receipt-side authority cache
or host callback can replace these Lean indices.

Every positive construction below is indexed by
`CredentialAuthorityState.authState domain pre`.  Consequently authorization,
capability membership, revocation, epochs, the request pre-root, and the patch
all consult the same canonical pre-cell.
-/
import Theory.CredentialAuthorityState

namespace Minidregg.Theory.CredentialAuthorityEffects

open IndexedProgram
open TypedAuthorization
open CredentialAuthorityState
open CredentialAuthorityFamily

/-! ## Common sealed family plumbing -/

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by simp

def sealedOnly : DisclosureDecision Unit Unit (fun _ => Unit) → Prop
  | .sealed => True
  | .reveal _ _ => False
  | .declassify _ _ _ => False

/-- Canonical operation wrappers use eager nullifier identifiers.  The same id
is also written to the canonical sparse nullifier plane by every patch. -/
abbrev OperationNullifier := Nat

/-- Exact generated patches are not merely well shaped: the public validator
can mint their `ValidatedPatch` token.  This is the common positive path used
by all four operation families. -/
theorem validated_of_exact {M : Materializer} {pre : Cell M}
    (patch : CellState.Patch schema Digest)
    (preRootExact : patch.expectedPreRoot = pre.root)
    (fieldsExact : patch.fieldFootprint = patch.namedFields)
    (resourcesExact : patch.resourceFootprint = patch.namedResources) :
    Nonempty (CellState.ValidatedPatch M pre patch) := by
  generalize outcomeExact : CellState.validate M pre patch = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      simp [CellState.validate, preRootExact, fieldsExact, resourcesExact] at outcomeExact

/-! ## Capability issuance -/

structure IssueDeclaration (kind : ResourceKind) where
  capability : Capability kind
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def IssueDeclaration.patch {kind : ResourceKind}
    (declaration : IssueDeclaration kind) : CellState.Patch schema Digest where
  expectedPreRoot := declaration.expectedPreRoot
  fieldFootprint :=
    { .capability kind declaration.capability.id,
      .nullifier declaration.operationNullifier }
  resourceFootprint := ∅
  fieldWrites :=
    [ { field := .capability kind declaration.capability.id
        value := some ⟨declaration.capability, []⟩ },
      { field := .nullifier declaration.operationNullifier
        value := true } ]
  resourceWrites := []

@[simp] theorem IssueDeclaration.patch_namedFields {kind : ResourceKind}
    (declaration : IssueDeclaration kind) :
    declaration.patch.namedFields = declaration.patch.fieldFootprint := by
  simp [IssueDeclaration.patch, CellState.Patch.namedFields]

@[simp] theorem IssueDeclaration.patch_namedResources {kind : ResourceKind}
    (declaration : IssueDeclaration kind) :
    declaration.patch.namedResources = declaration.patch.resourceFootprint := by
  simp [IssueDeclaration.patch, CellState.Patch.namedResources]

/-- Issuance is root-only, fresh, current-epoch, registered for revocation, and
single-use. -/
structure IssueEvidence {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) {kind : ResourceKind}
    (declaration : IssueDeclaration kind) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  slotFresh : readCapability pre kind declaration.capability.id = none
  nullifierFresh : isNullified pre declaration.operationNullifier = false
  rootParent : declaration.capability.parent = none
  rootSelf : declaration.capability.root = declaration.capability.id
  rootAncestors : declaration.capability.ancestors = ∅
  issuerCurrent : declaration.capability.issuerEpoch =
    issuerEpochAt pre declaration.capability.issuer
  policyCurrent : declaration.capability.policyEpoch =
    policyEpochAt pre declaration.capability.policyId
  selfRegistered : RevocationKey.capability declaration.capability.id ∈
    domain.revocationKeys
  channelsRegistered : ∀ channel ∈ declaration.capability.channels,
    RevocationKey.channel channel ∈ domain.revocationKeys
  selfLive : isRevoked pre (.capability declaration.capability.id) = false
  channelsLive : ∀ channel ∈ declaration.capability.channels,
    isRevoked pre (.channel channel) = false

def issueFamily {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {kind : ResourceKind} (codec : LawfulCodec (IssueDeclaration kind))
    (effectDigest : IssueDeclaration kind → Digest) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := IssueDeclaration kind
  declarationCodec := codec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => IssueEvidence domain pre declaration
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- Positive issuance path.  The validator token is derived from the generated
patch and the mode evidence's exact canonical pre-root. -/
noncomputable def acceptIssue
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec (IssueDeclaration kind))
    (effectDigest : IssueDeclaration kind → Digest)
    (declaration : IssueDeclaration kind)
    (authorization : Authorized portal (authState domain pre) request)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : IssueEvidence domain pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (issueFamily domain pre codec effectDigest) request pre declaration () where
  authorization := authorization
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact declaration.patch
    modeEvidence.preRootExact declaration.patch_namedFields.symm
      declaration.patch_namedResources.symm
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## Strict capability attenuation -/

structure AttenuateDeclaration (kind : ResourceKind) where
  child : Capability kind
  parentId : CapabilityId
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def descendedCapability {kind : ResourceKind} (child : Capability kind)
    (parent : StoredCapability kind) : StoredCapability kind :=
  ⟨child, parent.head :: parent.ancestry⟩

def AttenuateDeclaration.patch {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind)
    (parent : StoredCapability kind) : CellState.Patch schema Digest where
  expectedPreRoot := declaration.expectedPreRoot
  fieldFootprint :=
    { .capability kind declaration.child.id,
      .nullifier declaration.operationNullifier }
  resourceFootprint := ∅
  fieldWrites :=
    [ { field := .capability kind declaration.child.id
        value := some (descendedCapability declaration.child parent) },
      { field := .nullifier declaration.operationNullifier
        value := true } ]
  resourceWrites := []

@[simp] theorem AttenuateDeclaration.patch_namedFields {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind) :
    (declaration.patch parent).namedFields =
      (declaration.patch parent).fieldFootprint := by
  simp [AttenuateDeclaration.patch, CellState.Patch.namedFields]

@[simp] theorem AttenuateDeclaration.patch_namedResources {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind) :
    (declaration.patch parent).namedResources =
      (declaration.patch parent).resourceFootprint := by
  simp [AttenuateDeclaration.patch, CellState.Patch.namedResources]

/-- The parent snapshot is not trusted: it must be exactly the record in the
canonical pre-cell.  Its lineage is revalidated and the child edge is strict. -/
structure AttenuateEvidence {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind)
    (parent : StoredCapability kind) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  parentExact : readCapability pre kind declaration.parentId = some parent
  parentIdExact : parent.head.id = declaration.parentId
  parentLineageValid : LineageValid parent
  strict : declaration.child.StrictAttenuates parent.head
  childSlotFresh : readCapability pre kind declaration.child.id = none
  nullifierFresh : isNullified pre declaration.operationNullifier = false
  issuerCurrent : declaration.child.issuerEpoch =
    issuerEpochAt pre declaration.child.issuer
  policyCurrent : declaration.child.policyEpoch =
    policyEpochAt pre declaration.child.policyId
  selfRegistered : RevocationKey.capability declaration.child.id ∈
    domain.revocationKeys
  ancestorsRegistered : ∀ ancestor ∈ declaration.child.ancestors,
    RevocationKey.capability ancestor ∈ domain.revocationKeys
  channelsRegistered : ∀ channel ∈ declaration.child.channels,
    RevocationKey.channel channel ∈ domain.revocationKeys
  selfLive : isRevoked pre (.capability declaration.child.id) = false
  ancestorsLive : ∀ ancestor ∈ declaration.child.ancestors,
    isRevoked pre (.capability ancestor) = false
  channelsLive : ∀ channel ∈ declaration.child.channels,
    isRevoked pre (.channel channel) = false

def attenuateFamily {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {kind : ResourceKind} (codec : LawfulCodec (AttenuateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : AttenuateDeclaration kind → Digest) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := AttenuateDeclaration kind
  declarationCodec := codec
  Outcome := fun _ => StoredCapability kind
  outcomeCodec := fun _ => parentCodec
  ModeEvidence := fun declaration parent =>
    AttenuateEvidence domain pre declaration parent
  effectDigest := effectDigest
  patch := fun declaration parent => declaration.patch parent
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

noncomputable def acceptAttenuation
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec (AttenuateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : AttenuateDeclaration kind → Digest)
    (declaration : AttenuateDeclaration kind)
    (parent : StoredCapability kind)
    (authorization : Authorized portal (authState domain pre) request)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : AttenuateEvidence domain pre declaration parent) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (attenuateFamily domain pre codec parentCodec effectDigest)
      request pre declaration parent where
  authorization := authorization
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact (declaration.patch parent)
    modeEvidence.preRootExact (declaration.patch_namedFields parent).symm
      (declaration.patch_namedResources parent).symm
  disclosure := .sealed
  disclosureAllowed := trivial

theorem AttenuateEvidence.childLineageValid {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {kind : ResourceKind}
    {declaration : AttenuateDeclaration kind}
    {parent : StoredCapability kind}
    (evidence : AttenuateEvidence domain pre declaration parent) :
    LineageValid (descendedCapability declaration.child parent) :=
  .attenuate declaration.child parent.head parent.ancestry
    evidence.parentLineageValid evidence.strict

/-! ## Revocation -/

structure RevokeDeclaration where
  key : RevocationKey
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def RevokeDeclaration.patch
    (declaration : RevokeDeclaration) : CellState.Patch schema Digest where
  expectedPreRoot := declaration.expectedPreRoot
  fieldFootprint :=
    { .revoked declaration.key, .nullifier declaration.operationNullifier }
  resourceFootprint := ∅
  fieldWrites :=
    [ { field := .revoked declaration.key, value := true },
      { field := .nullifier declaration.operationNullifier, value := true } ]
  resourceWrites := []

@[simp] theorem RevokeDeclaration.patch_namedFields (declaration : RevokeDeclaration) :
    declaration.patch.namedFields = declaration.patch.fieldFootprint := by
  simp [RevokeDeclaration.patch, CellState.Patch.namedFields]

@[simp] theorem RevokeDeclaration.patch_namedResources (declaration : RevokeDeclaration) :
    declaration.patch.namedResources = declaration.patch.resourceFootprint := by
  simp [RevokeDeclaration.patch, CellState.Patch.namedResources]

structure RevokeEvidence {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) (declaration : RevokeDeclaration) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  registered : declaration.key ∈ domain.revocationKeys
  live : isRevoked pre declaration.key = false
  nullifierFresh : isNullified pre declaration.operationNullifier = false

def revokeFamily {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    (codec : LawfulCodec RevokeDeclaration)
    (effectDigest : RevokeDeclaration → Digest) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := RevokeDeclaration
  declarationCodec := codec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => RevokeEvidence domain pre declaration
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

noncomputable def acceptRevocation
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec RevokeDeclaration)
    (effectDigest : RevokeDeclaration → Digest)
    (declaration : RevokeDeclaration)
    (authorization : Authorized portal (authState domain pre) request)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : RevokeEvidence domain pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest) request pre declaration () where
  authorization := authorization
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact declaration.patch
    modeEvidence.preRootExact declaration.patch_namedFields.symm
      declaration.patch_namedResources.symm
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## Epoch rotation -/

inductive EpochTarget where
  | issuer (issuer : IssuerId)
  | policy (policy : PolicyId)
  | subjectKey (subject : SubjectId)
  deriving DecidableEq, Repr

def EpochTarget.field : EpochTarget → AuthorityField
  | EpochTarget.issuer issuerId => .issuerEpoch issuerId
  | EpochTarget.policy policyId => .policyEpoch policyId
  | EpochTarget.subjectKey subjectId => .subjectKeyEpoch subjectId

def EpochTarget.read {M : Materializer} (pre : Cell M) : EpochTarget → Epoch
  | EpochTarget.issuer issuerId => issuerEpochAt pre issuerId
  | EpochTarget.policy policyId => policyEpochAt pre policyId
  | EpochTarget.subjectKey subjectId => subjectKeyEpochAt pre subjectId

def EpochTarget.readAuth (state : AuthState) : EpochTarget → Epoch
  | EpochTarget.issuer issuerId => state.issuerEpoch issuerId
  | EpochTarget.policy policyId => state.policyEpoch policyId
  | EpochTarget.subjectKey subjectId => state.subjectKeyEpoch subjectId

@[simp] theorem EpochTarget.readAuth_authState {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (target : EpochTarget) :
    target.readAuth (authState domain pre) = target.read pre := by
  cases target <;> rfl

def EpochTarget.write (target : EpochTarget) (epoch : Epoch) :
    CellState.FieldWrite schema :=
  match target with
  | EpochTarget.issuer issuerId => ⟨.issuerEpoch issuerId, epoch⟩
  | EpochTarget.policy policyId => ⟨.policyEpoch policyId, epoch⟩
  | EpochTarget.subjectKey subjectId => ⟨.subjectKeyEpoch subjectId, epoch⟩

@[simp] theorem EpochTarget.write_field (target : EpochTarget) (epoch : Epoch) :
    (target.write epoch).field = target.field := by
  cases target <;> rfl

structure RotateEpochDeclaration where
  target : EpochTarget
  expectedEpoch : Epoch
  nextEpoch : Epoch
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

def RotateEpochDeclaration.patch
    (declaration : RotateEpochDeclaration) : CellState.Patch schema Digest where
  expectedPreRoot := declaration.expectedPreRoot
  fieldFootprint :=
    { declaration.target.field, .nullifier declaration.operationNullifier }
  resourceFootprint := ∅
  fieldWrites :=
    [ declaration.target.write declaration.nextEpoch,
      { field := .nullifier declaration.operationNullifier, value := true } ]
  resourceWrites := []

@[simp] theorem RotateEpochDeclaration.patch_namedFields
    (declaration : RotateEpochDeclaration) :
    declaration.patch.namedFields = declaration.patch.fieldFootprint := by
  simp [RotateEpochDeclaration.patch, CellState.Patch.namedFields]
  rfl

@[simp] theorem RotateEpochDeclaration.patch_namedResources
    (declaration : RotateEpochDeclaration) :
    declaration.patch.namedResources = declaration.patch.resourceFootprint := by
  simp [RotateEpochDeclaration.patch, CellState.Patch.namedResources]

structure RotateEpochEvidence {M : Materializer} (pre : Cell M)
    (declaration : RotateEpochDeclaration) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  currentExact : declaration.target.read pre = declaration.expectedEpoch
  successorExact : declaration.nextEpoch = declaration.expectedEpoch + 1
  nullifierFresh : isNullified pre declaration.operationNullifier = false

def rotateEpochFamily {M : Materializer} (pre : Cell M)
    (codec : LawfulCodec RotateEpochDeclaration)
    (effectDigest : RotateEpochDeclaration → Digest) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := RotateEpochDeclaration
  declarationCodec := codec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => RotateEpochEvidence pre declaration
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

noncomputable def acceptEpochRotation
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec RotateEpochDeclaration)
    (effectDigest : RotateEpochDeclaration → Digest)
    (declaration : RotateEpochDeclaration)
    (authorization : Authorized portal (authState domain pre) request)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : RotateEpochEvidence pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (rotateEpochFamily pre codec effectDigest) request pre declaration () where
  authorization := authorization
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact declaration.patch
    modeEvidence.preRootExact declaration.patch_namedFields.symm
      declaration.patch_namedResources.symm
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## The common canonical-pre theorem and atomic patch teeth -/

/-- A formulation without typeclass magic, suitable for every portal. -/
theorem authorization_consults_same_canonical_pre
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {family : SemanticEffectFamily schema M OperationNullifier}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre) family request pre declaration outcome) :
    request.preStateRoot = pre.root ∧
      (authState domain pre).capabilityRoot = pre.root ∧
      (authState domain pre).revocationRoot = pre.root :=
  ⟨accepted.preRootBound, rfl, rfl⟩

@[simp] theorem issue_post_capability_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (issueFamily domain pre codec effectDigest) request pre declaration ()) :
    accepted.prepared.post.logical.fields
        (.capability kind declaration.capability.id) =
      some ⟨declaration.capability, []⟩ := by
  simp [AcceptedCellEffect.prepared, CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, issueFamily,
    IssueDeclaration.patch]

@[simp] theorem issue_post_nullifier_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (issueFamily domain pre codec effectDigest) request pre declaration ()) :
    isNullified accepted.prepared.post declaration.operationNullifier = true := by
  simp [isNullified, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, issueFamily,
    IssueDeclaration.patch]

@[simp] theorem attenuation_post_capability_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (attenuateFamily domain pre codec parentCodec effectDigest)
      request pre declaration parent) :
    readCapability accepted.prepared.post kind declaration.child.id =
      some (descendedCapability declaration.child parent) := by
  simp [readCapability, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, attenuateFamily,
    AttenuateDeclaration.patch]

/-- The written child is not just present: its retained first-order ancestry is
validated by the exact strict edge and parent lineage read from canonical pre. -/
theorem attenuation_post_lineage_valid
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (attenuateFamily domain pre codec parentCodec effectDigest)
      request pre declaration parent) :
    ∃ stored,
      readCapability accepted.prepared.post kind declaration.child.id = some stored ∧
      LineageValid stored := by
  exact ⟨descendedCapability declaration.child parent,
    attenuation_post_capability_exact accepted,
    accepted.modeEvidence.childLineageValid⟩

@[simp] theorem revocation_post_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest) request pre declaration ()) :
    isRevoked accepted.prepared.post declaration.key = true := by
  simp [isRevoked, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, revokeFamily,
    RevokeDeclaration.patch]

/-- A committed revocation is immediately visible to the next canonical
authorization projection; there is no stale host revocation cache. -/
theorem revocation_post_is_authorizer_member
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest) request pre declaration ()) :
    declaration.key ∈ (authState domain accepted.prepared.post).revoked := by
  apply (mem_authState_revoked_iff domain accepted.prepared.post declaration.key).2
  exact ⟨accepted.modeEvidence.registered, revocation_post_exact accepted⟩

@[simp] theorem rotation_post_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (rotateEpochFamily pre codec effectDigest) request pre declaration ()) :
    declaration.target.read accepted.prepared.post = declaration.nextEpoch := by
  rcases declaration with ⟨target, expectedEpoch, nextEpoch, expectedPreRoot,
    operationNullifier⟩
  cases target <;>
    simp [EpochTarget.read, issuerEpochAt, policyEpochAt, subjectKeyEpochAt,
      AcceptedCellEffect.prepared, CanonicalTransition.PreparedTurn.ofValidatedPatch,
      CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
      CellState.materialize, CellState.applyFieldWrites, rotateEpochFamily,
      RotateEpochDeclaration.patch, EpochTarget.write]

/-- Epoch rotation changes the exact epoch read by the next authorization
judgment, not merely an auxiliary receipt field. -/
theorem rotation_post_is_authorizer_epoch
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (rotateEpochFamily pre codec effectDigest) request pre declaration ()) :
    declaration.target.readAuth (authState domain accepted.prepared.post) =
      declaration.nextEpoch := by
  rw [declaration.target.readAuth_authState]
  exact rotation_post_exact accepted

/-- Revocation acceptance changes only its exact revocation key and operation
nullifier; every other typed address is framed by the canonical delta. -/
theorem revoke_frame
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest) request pre declaration ())
    (field : AuthorityField)
    (outside : field ∉ declaration.patch.fieldFootprint) :
    accepted.prepared.post.logical.fields field = pre.logical.fields field :=
  accepted.field_frame field outside

/-- Every family exposes the exact eager nullifier that its atomic patch also
writes. -/
theorem revoke_nullifier_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest) request pre declaration ()) :
    accepted.prepared.nullifier = some declaration.operationNullifier := rfl

#print axioms AttenuateEvidence.childLineageValid
#print axioms authorization_consults_same_canonical_pre
#print axioms revocation_post_is_authorizer_member
#print axioms rotation_post_is_authorizer_epoch
#print axioms revoke_frame

end Minidregg.Theory.CredentialAuthorityEffects
