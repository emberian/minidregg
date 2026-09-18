/-
# Theory.CredentialAuthorityEffects -- canonical authority mutations

Issuance, strict attenuation, authorized subject delegation, revocation,
and epoch rotation are ordinary
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
import Theory.CredentialLineageAdmission

namespace Minidregg.Theory.CredentialAuthorityEffects

open IndexedProgram
open TypedAuthorization
open CredentialAuthorityState
open CredentialAuthorityFamily
open CredentialLineageAdmission

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

/-- The deployment fixes the authority-control resource and ambient identity
in first-order data.  Each operation derives its argument address from the
whole lawful declaration codec, its nonce from its eager nullifier, and its
root from the exact canonical authority cell. -/
structure RequestContext where
  authority : EffectRequestContext
  argsDigestBytes : List UInt8 → Digest

def RequestContext.request {Declaration : Type}
    (context : RequestContext) (codec : LawfulCodec Declaration)
    (effectDigest : Declaration → Digest) (preRoot : Digest)
    (nonce : Nat) (declaration : Declaration) : PackedEffectRequest :=
  ⟨context.authority.kind,
    { context.authority.request
        (context.argsDigestBytes (codec.encode declaration))
        (effectDigest declaration) preRoot with nonce := nonce }⟩

variable {context : RequestContext}

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
        value := some true } ]
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
  slotFresh : CapabilityIdFresh pre declaration.capability.id
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

theorem IssueEvidence.reject_existing_id {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {kind : ResourceKind}
    {declaration : IssueDeclaration kind}
    (mode : IssueEvidence domain pre declaration)
    (otherKind : ResourceKind) (existing : StoredCapability otherKind)
    (present : readCapability pre otherKind declaration.capability.id = some existing) :
    False := by
  rw [mode.slotFresh otherKind] at present
  cases present

def issueFamily {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {kind : ResourceKind} (codec : LawfulCodec (IssueDeclaration kind))
    (effectDigest : IssueDeclaration kind → Digest) (context : RequestContext) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := IssueDeclaration kind
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => IssueEvidence domain pre declaration
  Postcondition := fun declaration _ post => declaration.patch.ResultAt pre.logical post
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
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec (IssueDeclaration kind))
    (effectDigest : IssueDeclaration kind → Digest)
    (declaration : IssueDeclaration kind)
    (authorization : Authorized portal (authState domain pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : IssueEvidence domain pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (issueFamily domain pre codec effectDigest context) request pre declaration () where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact declaration.patch
    modeEvidence.preRootExact declaration.patch_namedFields.symm
      declaration.patch_namedResources.symm
  postcondition := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
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
  ⟨child, ⟨parent.head, .strict⟩ :: parent.ancestry⟩

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
        value := some true } ]
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

/-- Shared pre-state requirements for strict narrowing and explicit
subject delegation. Both use the same canonical lookup, anchored lineage,
across-kind identity freshness and current revocation/epoch planes. -/
structure DescentEvidence {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) {kind : ResourceKind} (expectedPreRoot : Digest)
    (parentId : CapabilityId) (child : Capability kind)
    (operationNullifier : OperationNullifier) (parent : StoredCapability kind) : Type where
  preRootExact : expectedPreRoot = pre.root
  parentExact : readCapability pre kind parentId = some parent
  parentIdExact : parent.head.id = parentId
  parentLineageValid : LineageValid parent
  parentLineageAnchored : LineageAnchored pre parent
  childSlotFresh : CapabilityIdFresh pre child.id
  nullifierFresh : isNullified pre operationNullifier = false
  issuerCurrent : child.issuerEpoch = issuerEpochAt pre child.issuer
  policyCurrent : child.policyEpoch = policyEpochAt pre child.policyId
  selfRegistered : RevocationKey.capability child.id ∈ domain.revocationKeys
  ancestorsRegistered : ∀ ancestor ∈ child.ancestors,
    RevocationKey.capability ancestor ∈ domain.revocationKeys
  channelsRegistered : ∀ channel ∈ child.channels,
    RevocationKey.channel channel ∈ domain.revocationKeys
  selfLive : isRevoked pre (.capability child.id) = false
  ancestorsLive : ∀ ancestor ∈ child.ancestors,
    isRevoked pre (.capability ancestor) = false
  channelsLive : ∀ channel ∈ child.channels,
    isRevoked pre (.channel channel) = false

theorem DescentEvidence.reject_existing_child {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {kind : ResourceKind}
    {expectedPreRoot : Digest} {parentId : CapabilityId} {child : Capability kind}
    {operationNullifier : OperationNullifier} {parent : StoredCapability kind}
    (mode : DescentEvidence domain pre expectedPreRoot parentId child operationNullifier parent)
    (otherKind : ResourceKind) (existing : StoredCapability otherKind)
    (present : readCapability pre otherKind child.id = some existing) : False := by
  rw [mode.childSlotFresh otherKind] at present
  cases present

theorem DescentEvidence.reject_spent_nullifier {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {kind : ResourceKind}
    {expectedPreRoot : Digest} {parentId : CapabilityId} {child : Capability kind}
    {operationNullifier : OperationNullifier} {parent : StoredCapability kind}
    (mode : DescentEvidence domain pre expectedPreRoot parentId child operationNullifier parent)
    (spent : isNullified pre operationNullifier = true) : False := by
  rw [mode.nullifierFresh] at spent
  cases spent

/-- Fresh capability production preserves every already-present capability,
even when storage kinds differ. This is the shared frame fact needed to keep
canonical ancestry anchored after appending a child. -/
theorem capabilityProduction_preserves_present {M : Materializer}
    {pre : Cell M} {patch : CellState.Patch schema Digest}
    {kind : ResourceKind} {identifier : CapabilityId} {nullifier : Nat}
    (validated : CellState.ValidatedPatch M pre patch)
    (footprint : patch.fieldFootprint = { .capability kind identifier, .nullifier nullifier })
    (fresh : CapabilityIdFresh pre identifier)
    (otherKind : ResourceKind) (otherId : CapabilityId)
    (stored : StoredCapability otherKind)
    (present : readCapability pre otherKind otherId = some stored) :
    readCapability validated.apply otherKind otherId = some stored := by
  have different : AuthorityField.capability otherKind otherId ≠ .capability kind identifier := by
    intro same
    have sameId : otherId = identifier := by injection same
    subst otherId
    rw [fresh otherKind] at present
    cases present
  calc
    readCapability validated.apply otherKind otherId =
        readCapability pre otherKind otherId :=
      validated.field_frame (.capability otherKind otherId) (by
        intro member
        rw [footprint] at member
        rcases Finset.mem_insert.mp member with same | singleton
        · exact different same
        · have impossible := Finset.mem_singleton.mp singleton
          cases impossible)
    _ = some stored := present

/-- The strict operation retains its original holder-narrowing relation. -/
structure AttenuateEvidence {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) {kind : ResourceKind}
    (declaration : AttenuateDeclaration kind) (parent : StoredCapability kind)
    extends DescentEvidence domain pre declaration.expectedPreRoot declaration.parentId
      declaration.child declaration.operationNullifier parent where
  strict : declaration.child.StrictAttenuates parent.head

theorem AttenuateEvidence.childLineageAnchored {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {kind : ResourceKind}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (evidence : AttenuateEvidence domain pre declaration parent)
    (validated : CellState.ValidatedPatch M pre (declaration.patch parent)) :
    LineageAnchored validated.apply (descendedCapability declaration.child parent) := by
  have preserved := capabilityProduction_preserves_present validated rfl evidence.childSlotFresh
  have parentPresent : readCapability pre kind parent.head.id = some parent := by
    rw [evidence.parentIdExact]
    exact evidence.parentExact
  change readCapability validated.apply kind parent.head.id = some parent ∧
    LineageAnchored validated.apply parent
  exact ⟨preserved kind parent.head.id parent parentPresent,
    evidence.parentLineageAnchored.of_present_reads_preserved preserved⟩

def attenuateFamily {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    {kind : ResourceKind} (codec : LawfulCodec (AttenuateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : AttenuateDeclaration kind → Digest) (context : RequestContext) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := AttenuateDeclaration kind
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => StoredCapability kind
  outcomeCodec := fun _ => parentCodec
  ModeEvidence := fun declaration parent =>
    AttenuateEvidence domain pre declaration parent
  Postcondition := fun declaration parent post =>
    (declaration.patch parent).ResultAt pre.logical post ∧
    LineageAnchored (CellState.materialize M post)
      (descendedCapability declaration.child parent)
  effectDigest := effectDigest
  patch := fun declaration parent => declaration.patch parent
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

noncomputable def acceptAttenuation
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec (AttenuateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : AttenuateDeclaration kind → Digest)
    (declaration : AttenuateDeclaration kind)
    (parent : StoredCapability kind)
    (authorization : Authorized portal (authState domain pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : AttenuateEvidence domain pre declaration parent) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (attenuateFamily domain pre codec parentCodec effectDigest context)
      request pre declaration parent := by
  let validated := Classical.choice <| validated_of_exact (declaration.patch parent)
    modeEvidence.preRootExact (declaration.patch_namedFields parent).symm
      (declaration.patch_namedResources parent).symm
  exact
    { authorization := authorization
      preStateBound := rfl
      requestBound := requestBound
      effectsDigestBound := requestDigestExact
      preRootBound := requestPreExact
      modeEvidence := modeEvidence
      validated := validated
      postcondition := ⟨validated.resultAt, modeEvidence.childLineageAnchored validated⟩
      disclosure := .sealed
      disclosureAllowed := trivial }

theorem AttenuateEvidence.childLineageValid {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {kind : ResourceKind}
    {declaration : AttenuateDeclaration kind}
    {parent : StoredCapability kind}
    (evidence : AttenuateEvidence domain pre declaration parent) :
    LineageValid (descendedCapability declaration.child parent) :=
  .attenuate declaration.child parent.head parent.ancestry
    evidence.parentLineageValid evidence.strict

/-! ## Explicit authorized subject delegation -/

structure DelegateDeclaration (kind : ResourceKind) where
  child : Capability kind
  parentId : CapabilityId
  target : ResourceId kind
  expectedPreRoot : Digest
  operationNullifier : OperationNullifier

/-- Ambient values are fixed by the receiving source before a complete request
is built. Target, verb, nonce, policy, arguments, effects and root are derived
from the typed declaration and actual pre-state, not a request callback. -/
structure DelegationContext where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  height : Height
  cost : Nat
  argsDigestBytes : List UInt8 → Digest

def DelegationContext.request (context : DelegationContext) {M : Materializer} {kind : ResourceKind}
    (codec : LawfulCodec (DelegateDeclaration kind))
    (effectDigest : DelegateDeclaration kind → Digest) (pre : Cell M)
    (declaration : DelegateDeclaration kind) : Request kind where
  domain := context.domain
  semantics := context.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := declaration.target
  verb := delegateVerb kind
  argsDigest := context.argsDigestBytes (codec.encode declaration)
  effectsDigest := effectDigest declaration
  nonce := declaration.operationNullifier
  height := context.height
  preStateRoot := pre.root
  policyId := declaration.child.policyId
  policyEpoch := declaration.child.policyEpoch
  policyRevision := policyRevisionAt pre declaration.child.policyId
  cost := context.cost

def delegatedCapability {kind : ResourceKind} (child : Capability kind)
    (parent : StoredCapability kind) (request : Request kind) : StoredCapability kind :=
  ⟨child, ⟨parent.head, .delegated request⟩ :: parent.ancestry⟩

def DelegateDeclaration.patch {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) : CellState.Patch schema Digest where
  expectedPreRoot := declaration.expectedPreRoot
  fieldFootprint :=
    { .capability kind declaration.child.id, .nullifier declaration.operationNullifier }
  resourceFootprint := ∅
  fieldWrites :=
    [ { field := .capability kind declaration.child.id
        value := some (delegatedCapability declaration.child parent request) },
      { field := .nullifier declaration.operationNullifier
        value := some true } ]
  resourceWrites := []

@[simp] theorem DelegateDeclaration.patch_namedFields {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) :
    (declaration.patch parent request).namedFields =
      (declaration.patch parent request).fieldFootprint := by
  simp [DelegateDeclaration.patch, CellState.Patch.namedFields]

@[simp] theorem DelegateDeclaration.patch_namedResources {kind : ResourceKind}
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (request : Request kind) :
    (declaration.patch parent request).namedResources =
      (declaration.patch parent request).resourceFootprint := by
  simp [DelegateDeclaration.patch, CellState.Patch.namedResources]

/-- The parent invocation is mandatory inside family mode evidence, not only
inside a convenience constructor. Its commitment is the one verified by the
same source portal's exact stored-capability check; an unrelated signature,
proof token or another capability cannot discharge `parentNamed`. -/
structure DelegationEvidence {M : Materializer} (domain : ProjectionUniverse)
    (pre : Cell M) (portal : Portal) (context : DelegationContext)
    {kind : ResourceKind} (codec : LawfulCodec (DelegateDeclaration kind))
    (effectDigest : DelegateDeclaration kind → Digest)
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    extends DescentEvidence domain pre declaration.expectedPreRoot declaration.parentId
      declaration.child declaration.operationNullifier parent where
  parentCommitment : Digest
  parentAuthorization : Authorized portal (authState domain pre)
    (context.request codec effectDigest pre declaration)
  parentNamed : parentAuthorization.evidence.capabilityValue =
    some (parent.head, parentCommitment)
  shape : DelegationShape (context.request codec effectDigest pre declaration)
    declaration.child parent.head

theorem DelegationEvidence.childLineageValid {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (evidence : DelegationEvidence domain pre portal context codec effectDigest declaration parent) :
    LineageValid (delegatedCapability declaration.child parent
      (context.request codec effectDigest pre declaration)) :=
  .delegate declaration.child parent.head parent.ancestry
    (context.request codec effectDigest pre declaration)
    evidence.parentLineageValid evidence.shape

theorem DelegationEvidence.childLineageAnchored {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (evidence : DelegationEvidence domain pre portal context codec effectDigest declaration parent)
    (validated : CellState.ValidatedPatch M pre
      (declaration.patch parent (context.request codec effectDigest pre declaration))) :
    LineageAnchored validated.apply (delegatedCapability declaration.child parent
      (context.request codec effectDigest pre declaration)) := by
  have preserved := capabilityProduction_preserves_present validated rfl evidence.childSlotFresh
  have parentPresent : readCapability pre kind parent.head.id = some parent := by
    rw [evidence.parentIdExact]
    exact evidence.parentExact
  change readCapability validated.apply kind parent.head.id = some parent ∧
    LineageAnchored validated.apply parent
  exact ⟨preserved kind parent.head.id parent parentPresent,
    evidence.parentLineageAnchored.of_present_reads_preserved preserved⟩

def delegateFamily {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    (portal : Portal) (context : DelegationContext) {kind : ResourceKind}
    (codec : LawfulCodec (DelegateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : DelegateDeclaration kind → Digest) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := DelegateDeclaration kind
  declarationCodec := codec
  pre := pre
  request := fun declaration =>
    ⟨kind, context.request codec effectDigest pre declaration⟩
  Outcome := fun _ => StoredCapability kind
  outcomeCodec := fun _ => parentCodec
  ModeEvidence := fun declaration parent =>
    DelegationEvidence domain pre portal context codec effectDigest declaration parent
  Postcondition := fun declaration parent post =>
    (declaration.patch parent (context.request codec effectDigest pre declaration)).ResultAt
      pre.logical post ∧
    LineageAnchored (CellState.materialize M post) (delegatedCapability declaration.child parent
      (context.request codec effectDigest pre declaration))
  effectDigest := effectDigest
  patch := fun declaration parent =>
    declaration.patch parent (context.request codec effectDigest pre declaration)
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- This constructor uses the exact parent grant already retained inside mode.
It accepts neither a caller-selected request nor replacement authorization. -/
noncomputable def acceptDelegation {M : Materializer}
    (domain : ProjectionUniverse) (pre : Cell M) (portal : Portal)
    (context : DelegationContext) {kind : ResourceKind}
    (codec : LawfulCodec (DelegateDeclaration kind))
    (parentCodec : LawfulCodec (StoredCapability kind))
    (effectDigest : DelegateDeclaration kind → Digest)
    (declaration : DelegateDeclaration kind) (parent : StoredCapability kind)
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (delegateFamily domain pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent := by
  let request := context.request codec effectDigest pre declaration
  let validated := Classical.choice <| validated_of_exact (declaration.patch parent request)
    mode.preRootExact (declaration.patch_namedFields parent request).symm
      (declaration.patch_namedResources parent request).symm
  exact
    { authorization := mode.parentAuthorization
      preStateBound := rfl
      requestBound := rfl
      effectsDigestBound := rfl
      preRootBound := rfl
      modeEvidence := mode
      validated := validated
      postcondition := ⟨validated.resultAt, mode.childLineageAnchored validated⟩
      disclosure := .sealed
      disclosureAllowed := trivial }

theorem DelegationEvidence.parent_use_verified {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent) :
    ∃ witness, portal.verifyCapabilityUse
      (context.request codec effectDigest pre declaration) parent.head
      mode.parentCommitment witness = true :=
  capability_evidence_requires_use mode.parentAuthorization.evidence
    parent.head mode.parentCommitment mode.parentNamed

theorem DelegationEvidence.reject_missing_delegate {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent)
    (missing : delegateVerb kind ∉ parent.head.scope.verbs) : False :=
  missing mode.shape.requires_delegate_verb

theorem DelegationEvidence.reject_non_capability_mode {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent)
    (notCapability : mode.parentAuthorization.evidence.capabilityValue = none) : False := by
  have named := mode.parentNamed
  rw [notCapability] at named
  cases named

section DelegationObligations

variable {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
  {portal : Portal} {context : DelegationContext} {kind : ResourceKind}
  {codec : LawfulCodec (DelegateDeclaration kind)}
  {effectDigest : DelegateDeclaration kind → Digest}
  {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}

/-- The mandatory mode opens and authorizes the same exact parent, whose full
retained suffix is checked against the same canonical pre-state. -/
theorem DelegationEvidence.parent_exact
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent) :
    readCapability pre kind declaration.parentId = some parent ∧
      mode.parentAuthorization.evidence.capabilityValue =
        some (parent.head, mode.parentCommitment) ∧
      LineageValid parent ∧ LineageAnchored pre parent :=
  ⟨mode.parentExact, mode.parentNamed, mode.parentLineageValid, mode.parentLineageAnchored⟩

theorem DelegationEvidence.reject_wrong_parent
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent)
    (actual : StoredCapability kind)
    (present : readCapability pre kind declaration.parentId = some actual)
    (different : actual ≠ parent) : False := by
  exact different (Option.some.inj (present.symm.trans mode.parentExact))

theorem DelegationEvidence.reject_wrong_grantor
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent)
    (different : parent.head.holder ≠ .subject context.subject) : False :=
  different mode.shape.grantor

theorem DelegationEvidence.reject_bearer_child
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent)
    (bearer : declaration.child.holder = .bearer) : False :=
  mode.shape.recipient bearer

theorem DelegationEvidence.child_bounds
    (mode : DelegationEvidence domain pre portal context codec effectDigest declaration parent) :
    Capability.LineageBounds declaration.child parent.head :=
  mode.shape.payload.lineageBounds

end DelegationObligations

@[simp] theorem delegation_post_capability_exact {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (delegateFamily domain pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent) :
    readCapability accepted.prepared.post kind declaration.child.id =
      some (delegatedCapability declaration.child parent
        (context.request codec effectDigest pre declaration)) := by
  simp [readCapability, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
    delegateFamily, DelegateDeclaration.patch]
  rfl

@[simp] theorem delegation_post_nullifier_exact {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (delegateFamily domain pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent) :
    isNullified accepted.prepared.post declaration.operationNullifier = true := by
  simp [isNullified, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
    delegateFamily, DelegateDeclaration.patch]

theorem delegation_post_lineage_valid {M : Materializer}
    {domain : ProjectionUniverse} {pre : Cell M} {portal : Portal}
    {context : DelegationContext} {kind : ResourceKind}
    {codec : LawfulCodec (DelegateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : DelegateDeclaration kind → Digest}
    {declaration : DelegateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (delegateFamily domain pre portal context codec parentCodec effectDigest)
      (context.request codec effectDigest pre declaration) pre declaration parent) :
    ∃ stored, readCapability accepted.prepared.post kind declaration.child.id = some stored ∧
      LineageValid stored ∧ LineageAnchored accepted.prepared.post stored := by
  exact ⟨_, delegation_post_capability_exact accepted,
    accepted.modeEvidence.childLineageValid, accepted.postcondition.2⟩

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
    [ { field := .revoked declaration.key, value := some true },
      { field := .nullifier declaration.operationNullifier, value := some true } ]
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
    (effectDigest : RevokeDeclaration → Digest) (context : RequestContext) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := RevokeDeclaration
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => RevokeEvidence domain pre declaration
  Postcondition := fun declaration _ post => declaration.patch.ResultAt pre.logical post
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

noncomputable def acceptRevocation
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec RevokeDeclaration)
    (effectDigest : RevokeDeclaration → Digest)
    (declaration : RevokeDeclaration)
    (authorization : Authorized portal (authState domain pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : RevokeEvidence domain pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest context) request pre declaration () where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact declaration.patch
    modeEvidence.preRootExact declaration.patch_namedFields.symm
      declaration.patch_namedResources.symm
  postcondition := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
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
  | EpochTarget.issuer issuerId => ⟨.issuerEpoch issuerId, some epoch⟩
  | EpochTarget.policy policyId => ⟨.policyEpoch policyId, some epoch⟩
  | EpochTarget.subjectKey subjectId => ⟨.subjectKeyEpoch subjectId, some epoch⟩

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
      { field := .nullifier declaration.operationNullifier, value := some true } ]
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

/-- Rotating a grant generation leaves that resource's selected policy source
unchanged in the ACTUAL joint post. A deliberate combined source-and-generation
change requires its own ordered batch semantics, not two same-pre writes. -/
def EpochTarget.SourceFramed (target : EpochTarget)
    (pre post : CellState.LogicalState schema) : Prop :=
  match target with
  | .policy policyId =>
      post.fields (.policyRevision policyId) = pre.fields (.policyRevision policyId) ∧
      ∀ revision, post.fields (.policyAddress policyId revision) =
        pre.fields (.policyAddress policyId revision)
  | _ => True

theorem RotateEpochDeclaration.source_framed {M : Materializer} {pre : Cell M}
    (declaration : RotateEpochDeclaration)
    (validated : CellState.ValidatedPatch M pre declaration.patch) :
    declaration.target.SourceFramed pre.logical validated.apply.logical := by
  cases target : declaration.target with
  | issuer _ => trivial
  | subjectKey _ => trivial
  | policy policy =>
      constructor
      · exact validated.field_frame (.policyRevision policy) (by
          change AuthorityField.policyRevision policy ∉
            ({declaration.target.field, .nullifier declaration.operationNullifier} :
              Finset AuthorityField)
          simp [target, EpochTarget.field])
      · intro revision
        exact validated.field_frame (.policyAddress policy revision) (by
          change AuthorityField.policyAddress policy revision ∉
            ({declaration.target.field, .nullifier declaration.operationNullifier} :
              Finset AuthorityField)
          simp [target, EpochTarget.field])

structure RotateEpochEvidence {M : Materializer} (pre : Cell M)
    (declaration : RotateEpochDeclaration) : Type where
  preRootExact : declaration.expectedPreRoot = pre.root
  currentExact : declaration.target.read pre = declaration.expectedEpoch
  successorExact : declaration.nextEpoch = declaration.expectedEpoch + 1
  nullifierFresh : isNullified pre declaration.operationNullifier = false

def rotateEpochFamily {M : Materializer} (pre : Cell M)
    (codec : LawfulCodec RotateEpochDeclaration)
    (effectDigest : RotateEpochDeclaration → Digest) (context : RequestContext) :
    SemanticEffectFamily schema M OperationNullifier where
  Declaration := RotateEpochDeclaration
  declarationCodec := codec
  pre := pre
  request := fun declaration => context.request codec effectDigest pre.root
    declaration.operationNullifier declaration
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => RotateEpochEvidence pre declaration
  Postcondition := fun declaration _ post =>
    declaration.patch.ResultAt pre.logical post ∧
    declaration.target.SourceFramed pre.logical post
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

noncomputable def acceptEpochRotation
    {M : Materializer} (domain : ProjectionUniverse) (pre : Cell M)
    (context : RequestContext)
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    (codec : LawfulCodec RotateEpochDeclaration)
    (effectDigest : RotateEpochDeclaration → Digest)
    (declaration : RotateEpochDeclaration)
    (authorization : Authorized portal (authState domain pre) request)
    (requestBound : (⟨kind, request⟩ : PackedEffectRequest) =
      context.request codec effectDigest pre.root declaration.operationNullifier declaration)
    (requestDigestExact : request.effectsDigest = effectDigest declaration)
    (requestPreExact : request.preStateRoot = pre.root)
    (modeEvidence : RotateEpochEvidence pre declaration) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (rotateEpochFamily pre codec effectDigest context) request pre declaration () where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := requestDigestExact
  preRootBound := requestPreExact
  modeEvidence := modeEvidence
  validated := Classical.choice <| validated_of_exact declaration.patch
    modeEvidence.preRootExact declaration.patch_namedFields.symm
      declaration.patch_namedResources.symm
  postcondition := ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩,
    declaration.source_framed _⟩
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
      (issueFamily domain pre codec effectDigest context) request pre declaration ()) :
    accepted.prepared.post.logical.fields
        (.capability kind declaration.capability.id) =
      some ⟨declaration.capability, []⟩ := by
  simp [AcceptedCellEffect.prepared, CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
    issueFamily,
    IssueDeclaration.patch]

@[simp] theorem issue_post_nullifier_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (issueFamily domain pre codec effectDigest context) request pre declaration ()) :
    isNullified accepted.prepared.post declaration.operationNullifier = true := by
  simp [isNullified, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
    issueFamily,
    IssueDeclaration.patch]

theorem issue_post_lineage_valid
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (IssueDeclaration kind)}
    {effectDigest : IssueDeclaration kind → Digest}
    {declaration : IssueDeclaration kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (issueFamily domain pre codec effectDigest context) request pre declaration ()) :
    ∃ stored, readCapability accepted.prepared.post kind declaration.capability.id = some stored ∧
      LineageValid stored ∧ LineageAnchored accepted.prepared.post stored := by
  refine ⟨⟨declaration.capability, []⟩, issue_post_capability_exact accepted, ?_, trivial⟩
  exact .root declaration.capability accepted.modeEvidence.rootParent
    accepted.modeEvidence.rootSelf accepted.modeEvidence.rootAncestors

@[simp] theorem attenuation_post_capability_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (attenuateFamily domain pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    readCapability accepted.prepared.post kind declaration.child.id =
      some (descendedCapability declaration.child parent) := by
  simp [readCapability, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
    attenuateFamily,
    AttenuateDeclaration.patch]
  rfl

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
      (attenuateFamily domain pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    ∃ stored,
      readCapability accepted.prepared.post kind declaration.child.id = some stored ∧
      LineageValid stored := by
  exact ⟨descendedCapability declaration.child parent,
    attenuation_post_capability_exact accepted,
    accepted.modeEvidence.childLineageValid⟩

/-- Strict descent also preserves the exact retained canonical parent chain
in the actual post-cell, including when the parent already has mixed lineage. -/
theorem attenuation_post_lineage_anchored
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (StoredCapability kind)}
    {effectDigest : AttenuateDeclaration kind → Digest}
    {declaration : AttenuateDeclaration kind} {parent : StoredCapability kind}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (attenuateFamily domain pre codec parentCodec effectDigest context)
      request pre declaration parent) :
    LineageAnchored accepted.prepared.post (descendedCapability declaration.child parent) :=
  accepted.postcondition.2

@[simp] theorem revocation_post_exact
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RevokeDeclaration}
    {effectDigest : RevokeDeclaration → Digest}
    {declaration : RevokeDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (revokeFamily domain pre codec effectDigest context) request pre declaration ()) :
    isRevoked accepted.prepared.post declaration.key = true := by
  simp [isRevoked, AcceptedCellEffect.prepared,
    CanonicalTransition.PreparedTurn.ofValidatedPatch,
    CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
    CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
    revokeFamily,
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
      (revokeFamily domain pre codec effectDigest context) request pre declaration ()) :
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
      (rotateEpochFamily pre codec effectDigest context) request pre declaration ()) :
    declaration.target.read accepted.prepared.post = declaration.nextEpoch := by
  rcases declaration with ⟨target, expectedEpoch, nextEpoch, expectedPreRoot,
    operationNullifier⟩
  cases target <;>
    simp [EpochTarget.read, issuerEpochAt, policyEpochAt, subjectKeyEpochAt,
      AcceptedCellEffect.prepared, CanonicalTransition.PreparedTurn.ofValidatedPatch,
      CanonicalTransition.CellDelta.ofValidatedPatch, CellState.ValidatedPatch.apply,
      CellState.materialize, CellState.applyFieldWrites, CellState.FieldStore.assign,
      rotateEpochFamily,
      RotateEpochDeclaration.patch, EpochTarget.write]

/-- The family postcondition retains source framing through joint composition,
not merely on the standalone patch that initially produced the token. -/
theorem rotation_joint_post_source_framed
    {M : Materializer} {pre : Cell M}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration} {post : CellState.LogicalState schema}
    (postcondition : (rotateEpochFamily pre codec effectDigest context).Postcondition
      declaration () post) :
    declaration.target.SourceFramed pre.logical post := postcondition.2

theorem rotation_post_source_framed
    {M : Materializer} {domain : ProjectionUniverse} {pre : Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec RotateEpochDeclaration}
    {effectDigest : RotateEpochDeclaration → Digest}
    {declaration : RotateEpochDeclaration}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := authState domain pre)
      (rotateEpochFamily pre codec effectDigest context) request pre declaration ()) :
    declaration.target.SourceFramed pre.logical accepted.prepared.post.logical :=
  accepted.postcondition.2

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
      (rotateEpochFamily pre codec effectDigest context) request pre declaration ()) :
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
      (revokeFamily domain pre codec effectDigest context) request pre declaration ())
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
      (revokeFamily domain pre codec effectDigest context) request pre declaration ()) :
    accepted.prepared.nullifier = some declaration.operationNullifier := rfl

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.AttenuateEvidence.childLineageValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AttenuateEvidence.childLineageValid
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.authorization_consults_same_canonical_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorization_consults_same_canonical_pre
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.revocation_post_is_authorizer_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revocation_post_is_authorizer_member
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.rotation_post_is_authorizer_epoch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rotation_post_is_authorizer_epoch
/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.revoke_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoke_frame

end Minidregg.Theory.CredentialAuthorityEffects
