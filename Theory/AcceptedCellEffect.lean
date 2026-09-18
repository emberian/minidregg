/-
# Theory.AcceptedCellEffect -- evidence-bearing effects over canonical cells

An accepted semantic effect joins one common authorization request to one
first-order declaration, one mode-indexed outcome/evidence package, and the
validated typed patch which determines its canonical post-state.  Private
ZK/MPC/FHE computations are instances of this join; they are not extra turn
modes and cannot be attached to an already committed receipt.

The exact canonical pre-cell and complete source-derived request are mandatory
family indices. A generic accepted token cannot substitute a different state
with the same root or relabel a declaration with an unrelated authorized request.

Disclosure is an independent decision.  The default is sealed.  A reveal or
declassification carries authorization indexed by its exact release value.
Receipt events are projections of an accepted effect and confer no independent
construction path.
-/
import Theory.CanonicalTransition
import Theory.PrivateComputationDeclaration

namespace Minidregg.Theory

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalTransition

universe u v w x y z

/-! ## Source-derived postconditions -/

/-- The produced part of a patch has its exact source-derived result in a
candidate post. Unrelated fields and packages remain unconstrained here, so
independent effects can compose. Families with additional post invariants
must retain those invariants alongside this relation in `Postcondition`.

This uses the existing canonical write interpretation. It is not an alternate
executor, a supplied Boolean, or equality of whole states. -/
def CellState.Patch.ResultAt
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (pre : CellState.LogicalState S) (patch : CellState.Patch S Digest)
    (post : CellState.LogicalState S) : Prop :=
  (∀ field ∈ patch.fieldFootprint,
    post.fields field =
      CellState.applyFieldWrites patch.fieldWrites pre.fields field) ∧
  (∀ resource ∈ patch.resourceFootprint,
    post.resources resource =
      CellState.applyResourceWrites patch.resourceWrites pre.resources resource)

/-- A verifier-minted canonical patch always realizes its own produced
result. The same relation can later be required at a jointly composed post. -/
theorem CellState.ValidatedPatch.resultAt
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {pre : CellState.Materialized M}
    {patch : CellState.Patch S Digest}
    (validated : CellState.ValidatedPatch M pre patch) :
    patch.ResultAt pre.logical validated.apply.logical := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## Independent disclosure decisions -/

/-- What this accepted effect actually discloses.  Release authorization is
indexed by the exact release; a declassification additionally retains its
first-order authority.  `sealed` is deliberately available for every family. -/
inductive DisclosureDecision
    (Release DeclassificationAuthority : Type y)
    (ReleaseAuthorization : Release → Type z) : Type (max y z) where
  | sealed
  | reveal (release : Release) (authorization : ReleaseAuthorization release)
  | declassify (authority : DeclassificationAuthority) (release : Release)
      (authorization : ReleaseAuthorization release)

/-- Absence of disclosure is the default; constructing a family never creates
a release merely because a computation completed. -/
instance DisclosureDecision.instInhabited
    {Release DeclassificationAuthority : Type y}
    {ReleaseAuthorization : Release → Type z} :
    Inhabited (DisclosureDecision Release DeclassificationAuthority
      ReleaseAuthorization) :=
  ⟨.sealed⟩

/-! ## First-order typed semantic effect families -/

/-- A typed request together with its resource kind.  Equality here retains
the complete request, including the typed target and verb; it is not equality
of a digest of that request. -/
abbrev PackedEffectRequest := (kind : ResourceKind) × Request kind

/-- First-order ambient authority data for generic computation adapters.
Arguments, effects, and the pre-state root are deliberately absent: the family
derives those three slots from its declaration and exact canonical pre-cell.
The target and verb are fixed by the adapter's source declaration, not supplied
by an untrusted request-to-request callback. -/
structure EffectRequestContext where
  kind : ResourceKind
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  target : ResourceId kind
  verb : Verb kind
  nonce : Nat
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch
  policyRevision : PolicyRevision
  cost : Nat

def EffectRequestContext.request (context : EffectRequestContext)
    (argsDigest effectsDigest preStateRoot : Digest) : Request context.kind where
  domain := context.domain
  semantics := context.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := context.target
  verb := context.verb
  argsDigest := argsDigest
  effectsDigest := effectsDigest
  nonce := context.nonce
  height := context.height
  preStateRoot := preStateRoot
  policyId := context.policyId
  policyEpoch := context.policyEpoch
  policyRevision := context.policyRevision
  cost := context.cost

/-- A semantic family separates first-order boundary data from its typed Lean
meaning.  The declaration and each dependent outcome have lawful codecs.  A
family supplies the unique patch, effect digest, optional eager nullifier, and
the exact types of evidence and release authority for each declaration/outcome.

This is trusted Lean semantics, not a callback ABI: an implementation may
produce candidate data, but it cannot replace these indices or projections. -/
structure SemanticEffectFamily
    (S : CellState.Schema.{u, v, w, x})
    (M : CellState.Materializer S Digest) (Nullifier : Type y) where
  Declaration : Type z
  declarationCodec : LawfulCodec Declaration
  /-- The exact canonical cell read by this family's trusted semantics.
  Root equality is not a substitute for equality of this value. -/
  pre : CellState.Materialized M
  /-- One complete, source-derived request per declaration.  Every accepted
  token, including a directly constructed generic leg, must equal this value. -/
  request : Declaration → PackedEffectRequest
  Outcome : Declaration → Type z
  outcomeCodec : (declaration : Declaration) → LawfulCodec (Outcome declaration)
  ModeEvidence : (declaration : Declaration) → Outcome declaration → Type z
  /-- The source's persistent output obligations, evaluated at an actual
  canonical post. Every local acceptance and every joint installation must
  establish these same obligations. The registered source family fixes this
  relation; an incoming host request cannot choose it. -/
  Postcondition : (declaration : Declaration) → Outcome declaration →
    CellState.LogicalState S → Prop
  effectDigest : Declaration → Digest
  patch : (declaration : Declaration) → Outcome declaration → CellState.Patch S Digest
  nullifier : (declaration : Declaration) → Outcome declaration → Option Nullifier
  Release : (declaration : Declaration) → Outcome declaration → Type z
  DeclassificationAuthority : (declaration : Declaration) →
    Outcome declaration → Type z
  ReleaseAuthorization : (declaration : Declaration) →
    (outcome : Outcome declaration) → Release declaration outcome → Type z
  DisclosureAllowed : (declaration : Declaration) →
    (outcome : Outcome declaration) →
    DisclosureDecision (Release declaration outcome)
      (DeclassificationAuthority declaration outcome)
      (ReleaseAuthorization declaration outcome) → Prop

/-! ## The common accepted-effect token -/

/-- The sole positive semantic join. The complete common authorization request
equals the family-selected source request, and the actual pre-cell equals the
family's canonical pre-cell. Digest and root checks remain explicit as well.
The validated patch determines the
post-cell and both footprints; there are no independently supplied versions. -/
structure AcceptedCellEffect
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    (request : Request kind) (pre : CellState.Materialized M)
    (declaration : family.Declaration)
    (outcome : family.Outcome declaration) : Type (max u v w x y z) where
  authorization : Authorized portal authState request
  preStateBound : pre = family.pre
  requestBound : (⟨kind, request⟩ : PackedEffectRequest) = family.request declaration
  effectsDigestBound : request.effectsDigest = family.effectDigest declaration
  preRootBound : request.preStateRoot = pre.root
  modeEvidence : family.ModeEvidence declaration outcome
  validated : CellState.ValidatedPatch M pre (family.patch declaration outcome)
  postcondition : family.Postcondition declaration outcome validated.apply.logical
  disclosure : DisclosureDecision (family.Release declaration outcome)
    (family.DeclassificationAuthority declaration outcome)
    (family.ReleaseAuthorization declaration outcome)
  disclosureAllowed : family.DisclosureAllowed declaration outcome disclosure

namespace AcceptedCellEffect

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}

/-- All request projections inherit exact equality; no digest reflection or
collision-resistance premise is used. -/
theorem request_projection {α : Sort*}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (projection : PackedEffectRequest → α) :
    projection ⟨kind, request⟩ = projection (family.request declaration) :=
  congrArg projection accepted.requestBound

theorem pre_logical_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    pre.logical = family.pre.logical :=
  congrArg CellState.Materialized.logical accepted.preStateBound

theorem request_kind_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    kind = (family.request declaration).1 :=
  accepted.request_projection Sigma.fst

theorem request_target_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    (⟨kind, request.target⟩ : (k : ResourceKind) × ResourceId k) =
      ⟨(family.request declaration).1, (family.request declaration).2.target⟩ :=
  accepted.request_projection
    (fun packed => (⟨packed.1, packed.2.target⟩ : (k : ResourceKind) × ResourceId k))

theorem request_verb_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    (⟨kind, request.verb⟩ : (k : ResourceKind) × Verb k) =
      ⟨(family.request declaration).1, (family.request declaration).2.verb⟩ :=
  accepted.request_projection
    (fun packed => (⟨packed.1, packed.2.verb⟩ : (k : ResourceKind) × Verb k))

theorem request_domain_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.domain = (family.request declaration).2.domain :=
  accepted.request_projection (fun packed => packed.2.domain)

theorem request_semantics_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.semantics = (family.request declaration).2.semantics :=
  accepted.request_projection (fun packed => packed.2.semantics)

theorem request_federation_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.federation = (family.request declaration).2.federation :=
  accepted.request_projection (fun packed => packed.2.federation)

theorem request_subject_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.subject = (family.request declaration).2.subject :=
  accepted.request_projection (fun packed => packed.2.subject)

theorem request_subjectKeyEpoch_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.subjectKeyEpoch = (family.request declaration).2.subjectKeyEpoch :=
  accepted.request_projection (fun packed => packed.2.subjectKeyEpoch)

theorem request_argsDigest_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.argsDigest = (family.request declaration).2.argsDigest :=
  accepted.request_projection (fun packed => packed.2.argsDigest)

theorem request_effectsDigest_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.effectsDigest = (family.request declaration).2.effectsDigest :=
  accepted.request_projection (fun packed => packed.2.effectsDigest)

theorem request_nonce_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.nonce = (family.request declaration).2.nonce :=
  accepted.request_projection (fun packed => packed.2.nonce)

theorem request_height_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.height = (family.request declaration).2.height :=
  accepted.request_projection (fun packed => packed.2.height)

theorem request_preStateRoot_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.preStateRoot = (family.request declaration).2.preStateRoot :=
  accepted.request_projection (fun packed => packed.2.preStateRoot)

theorem request_policyId_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.policyId = (family.request declaration).2.policyId :=
  accepted.request_projection (fun packed => packed.2.policyId)

theorem request_policyEpoch_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.policyEpoch = (family.request declaration).2.policyEpoch :=
  accepted.request_projection (fun packed => packed.2.policyEpoch)

theorem request_policyRevision_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.policyRevision = (family.request declaration).2.policyRevision :=
  accepted.request_projection (fun packed => packed.2.policyRevision)

theorem request_cost_exact
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    request.cost = (family.request declaration).2.cost :=
  accepted.request_projection (fun packed => packed.2.cost)
/-- A different request cannot become an accepted effect by bypassing a
family's convenience constructor. -/
theorem no_accepted_of_request_mismatch
    (mismatch : (⟨kind, request⟩ : PackedEffectRequest) ≠ family.request declaration) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :=
  ⟨fun accepted => mismatch accepted.requestBound⟩

/-- This refusal concerns the actual canonical state, including at a colliding
root.  A captured-state family cannot be applied to a different pre-cell. -/
theorem no_accepted_of_pre_mismatch (mismatch : pre ≠ family.pre) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :=
  ⟨fun accepted => mismatch accepted.preStateBound⟩

/-- The canonical prepared turn is derived from the accepted validated patch.
It cannot disagree about post-state, roots, footprints, or eager nullifier. -/
def prepared
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    PreparedTurn M pre Nullifier :=
  PreparedTurn.ofValidatedPatch accepted.validated
    (family.nullifier declaration outcome)

@[simp] theorem prepared_post
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    accepted.prepared.post = accepted.validated.apply :=
  rfl

@[simp] theorem prepared_preRoot
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    accepted.prepared.preRoot = request.preStateRoot :=
  accepted.preRootBound.symm

@[simp] theorem prepared_fieldFootprint
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    accepted.prepared.delta.fieldFootprint =
      (family.patch declaration outcome).fieldFootprint :=
  rfl

@[simp] theorem prepared_resourceFootprint
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    accepted.prepared.delta.resourceFootprint =
      (family.patch declaration outcome).resourceFootprint :=
  rfl

@[simp] theorem prepared_nullifier
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    accepted.prepared.nullifier = family.nullifier declaration outcome :=
  rfl

/-- Canonical field-frame fact inherited from the one validated patch. -/
theorem field_frame
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (field : S.Field)
    (outside : field ∉ (family.patch declaration outcome).fieldFootprint) :
    accepted.prepared.post.logical.fields field = pre.logical.fields field :=
  accepted.prepared.delta.fieldFrame field (by
    simpa only [prepared_fieldFootprint] using outside)

/-- Canonical resource-frame fact inherited from the one validated patch. -/
theorem resource_frame
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (resource : S.Resource)
    (outside : resource ∉ (family.patch declaration outcome).resourceFootprint) :
    accepted.prepared.post.logical.resources resource =
      pre.logical.resources resource :=
  accepted.prepared.delta.resourceFrame resource (by
    simpa only [prepared_resourceFootprint] using outside)

/-- Any changed field is in the exact family patch footprint. -/
theorem field_changed_only_declared
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (field : S.Field)
    (changed : accepted.prepared.post.logical.fields field ≠
      pre.logical.fields field) :
    field ∈ (family.patch declaration outcome).fieldFootprint := by
  simpa only [prepared_fieldFootprint] using
    accepted.prepared.delta.field_changed_only_declared field changed

/-- Any changed resource package is in the exact family patch footprint. -/
theorem resource_changed_only_declared
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (resource : S.Resource)
    (changed : accepted.prepared.post.logical.resources resource ≠
      pre.logical.resources resource) :
    resource ∈ (family.patch declaration outcome).resourceFootprint := by
  simpa only [prepared_resourceFootprint] using
    accepted.prepared.delta.resource_changed_only_declared resource changed

end AcceptedCellEffect

/-! ## Receipt projection after acceptance -/

/-- Receipt-visible evidence for an accepted effect.  The constructor is
private: the only public creation path below consumes `AcceptedCellEffect`.
This record is a projection and is not a second admission judgment. -/
structure ReceiptEvent
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier) :
    Type (max u v w x y z) where
  private mk ::
  kind : ResourceKind
  request : Request kind
  declaration : family.Declaration
  outcome : family.Outcome declaration
  modeEvidence : family.ModeEvidence declaration outcome
  disclosure : DisclosureDecision (family.Release declaration outcome)
    (family.DeclassificationAuthority declaration outcome)
    (family.ReleaseAuthorization declaration outcome)
  effectDigest : Digest
  preRoot : Digest
  postRoot : Digest
  fieldFootprint : Finset S.Field
  resourceFootprint : Finset S.Resource
  requestBound : (⟨kind, request⟩ : PackedEffectRequest) = family.request declaration
  canonicalPreRootBound : preRoot = family.pre.root
  effectsDigestBound : request.effectsDigest = effectDigest
  declarationDigestBound : effectDigest = family.effectDigest declaration
  requestPreRootBound : request.preStateRoot = preRoot

/-- Accepted effects alone project receipt events.  In particular, a bare mode
proof or private completion cannot augment an unrelated committed receipt. -/
def AcceptedCellEffect.toReceiptEvent
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    ReceiptEvent (M := M) family where
  kind := kind
  request := request
  declaration := declaration
  outcome := outcome
  modeEvidence := accepted.modeEvidence
  disclosure := accepted.disclosure
  effectDigest := family.effectDigest declaration
  preRoot := pre.root
  postRoot := accepted.prepared.postRoot
  fieldFootprint := accepted.prepared.delta.fieldFootprint
  resourceFootprint := accepted.prepared.delta.resourceFootprint
  requestBound := accepted.requestBound
  canonicalPreRootBound := congrArg CellState.Materialized.root accepted.preStateBound
  effectsDigestBound := accepted.effectsDigestBound
  declarationDigestBound := rfl
  requestPreRootBound := accepted.preRootBound

@[simp] theorem AcceptedCellEffect.toReceiptEvent_postRoot
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration} {outcome : family.Outcome declaration}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome) :
    accepted.toReceiptEvent.postRoot = accepted.prepared.postRoot :=
  rfl

/-! ## Authoritative release-free ZK/MPC/FHE computation family -/

namespace ComputationCellEffect

variable
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Relation BridgeName CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness OutputCommitment
      PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins : Type z}

/-- Kernel projections for a pure sealed-computation declaration.  The request
itself owns the nullifier and exact footprint.  The adapter supplies only the
canonical patch/digest interpretation and an explicit realization relation for
the request's typed resource effects. -/
structure Adapter
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins) where
  requestContext : EffectRequestContext
  requestCodec : LawfulCodec declaration.Request
  resultCodec : LawfulCodec declaration.Result
  requestDigestBytes : List UInt8 → Digest
  effectIntentCodec : LawfulCodec (List ResourceEffect × Footprint × Option Nullifier)
  effectDigestBytes : List UInt8 → Digest
  patch : declaration.Request → declaration.Result → CellState.Patch S Digest
  fieldFootprint : Footprint → Finset S.Field
  resourceFootprint : Footprint → Finset S.Resource
  RealizesResourceEffects : declaration.Request → declaration.Result →
    CellState.Patch S Digest → Prop
  resourceEffectsRealized : ∀ request result,
    RealizesResourceEffects request result (patch request result)
  fieldFootprintExact : ∀ request result,
    (patch request result).fieldFootprint = fieldFootprint request.footprint
  resourceFootprintExact : ∀ request result,
    (patch request result).resourceFootprint = resourceFootprint request.footprint

/-- The argument digest is structurally computed from the lawful encoding of
the entire core request. -/
def Adapter.completeRequestDigest
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins}
    (adapter : Adapter (S := S) declaration) (request : declaration.Request) : Digest :=
  adapter.requestDigestBytes (adapter.requestCodec.encode request)

/-- The effect digest is structurally computed from the lawful encoding of the
exact typed resource effects, declared footprint, and eager nullifier. -/
def Adapter.completeEffectDigest
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins}
    (adapter : Adapter (S := S) declaration) (request : declaration.Request) : Digest :=
  adapter.effectDigestBytes <|
    adapter.effectIntentCodec.encode
      (request.resourceEffects, request.footprint, request.nullifier)

/-- Pure computation is a semantic effect family whose only disclosure type is
empty.  Mode evidence is the exact release-free completion; the eager
nullifier is projected from the request rather than supplied by another path. -/
def family
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    (pre : CellState.Materialized M) :
    SemanticEffectFamily.{u, v, w, x, z, z} S M Nullifier where
  Declaration := declaration.Request
  declarationCodec := adapter.requestCodec
  pre := pre
  request := fun request => ⟨adapter.requestContext.kind,
    adapter.requestContext.request (adapter.completeRequestDigest request)
      (adapter.completeEffectDigest request) pre.root⟩
  Outcome := fun _ => declaration.Result
  outcomeCodec := fun _ => adapter.resultCodec
  ModeEvidence := fun request result => declaration.Completion request result
  Postcondition := fun request result post =>
    (adapter.patch request result).ResultAt pre.logical post
  effectDigest := adapter.completeEffectDigest
  patch := adapter.patch
  nullifier := fun request _ => request.nullifier
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => nomatch release
  DisclosureAllowed := fun _ _ disclosure =>
    match disclosure with
    | .sealed => True
    | .reveal release _ => nomatch release
    | .declassify authority _ _ => nomatch authority

/-- Compatibility view of an accepted computation. The nested common token
already forces the entire request, including `argsDigest`; the repeated
equation below is retained only for existing source consumers. -/
structure Accepted
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    (commonRequest : Request kind) (pre : CellState.Materialized M)
    (request : declaration.Request) (result : declaration.Result) where
  cellEffect : AcceptedCellEffect (portal := portal) (authState := authState)
    (family declaration adapter pre) commonRequest pre request result
  argsDigestBound : commonRequest.argsDigest = adapter.completeRequestDigest request

/-- There is no value in the release carrier of a pure computation family. -/
theorem family_no_release
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {pre : CellState.Materialized M}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    (request : declaration.Request) (result : declaration.Result)
    (release : (family (M := M) declaration adapter pre).Release request result) : False :=
  nomatch release

/-- The positive kernel join for sealed computation.  Disclosure is fixed to
`.sealed`; callers cannot supply a decision or a release-bearing witness. -/
def accept
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (authorization : Authorized portal authState commonRequest)
    (requestBound : (⟨kind, commonRequest⟩ : PackedEffectRequest) =
      (family declaration adapter pre).request request)
    (argsDigestBound : commonRequest.argsDigest = adapter.completeRequestDigest request)
    (effectsDigestBound : commonRequest.effectsDigest = adapter.completeEffectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : declaration.Completion request result)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request result)) :
    Accepted (portal := portal) (authState := authState)
      declaration adapter commonRequest pre request result where
  cellEffect := {
    authorization := authorization
    preStateBound := rfl
    requestBound := requestBound
    effectsDigestBound := effectsDigestBound
    preRootBound := preRootBound
    modeEvidence := completion
    validated := validated
    postcondition := validated.resultAt
    disclosure := .sealed
    disclosureAllowed := trivial
  }
  argsDigestBound := argsDigestBound

/-- Every accepted pure computation is sealed by construction. -/
theorem accepted_disclosure_sealed
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      (family declaration adapter pre) commonRequest pre request result) :
    accepted.disclosure = .sealed := by
  cases accepted.disclosure with
  | sealed => rfl
  | reveal release _ => exact nomatch release
  | declassify authority _ _ => exact nomatch authority

/-- The authoritative wrapper therefore cannot carry or select a release. -/
theorem Accepted.disclosure_sealed
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (accepted : Accepted (portal := portal) (authState := authState)
      declaration adapter commonRequest pre request result) :
    accepted.cellEffect.disclosure = .sealed :=
  accepted_disclosure_sealed declaration adapter accepted.cellEffect

@[simp] theorem accepted_field_footprint
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      (family declaration adapter pre) commonRequest pre request result) :
    accepted.prepared.delta.fieldFootprint = adapter.fieldFootprint request.footprint := by
  exact adapter.fieldFootprintExact request result

@[simp] theorem accepted_resource_footprint
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      (family declaration adapter pre) commonRequest pre request result) :
    accepted.prepared.delta.resourceFootprint = adapter.resourceFootprint request.footprint := by
  exact adapter.resourceFootprintExact request result

@[simp] theorem accepted_nullifier
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      (family declaration adapter pre) commonRequest pre request result) :
    accepted.prepared.nullifier = request.nullifier :=
  rfl

theorem accepted_resource_effects_realized
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)
    (adapter : Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (_accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      (family declaration adapter pre) commonRequest pre request result) :
    adapter.RealizesResourceEffects request result (adapter.patch request result) :=
  adapter.resourceEffectsRealized request result

end ComputationCellEffect

/-! ## Legacy release-coupled private family (compatibility only) -/

namespace PrivateCellEffect

variable
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose BridgeName AuthorizationContext
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      AuthorizationWitness OutputCommitment PrivateOutput OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority
      Release : Type z}
    (privateDeclaration : PrivateComputationDeclaration language mode Observer Policy
      Recipient Purpose BridgeName AuthorizationContext CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness AuthorizationWitness OutputCommitment
      PrivateOutput OutputSourceWitness OutputTargetWitness
      ReleaseAuthorizationWitness DeclassificationAuthority Release)

/-- The private adapter fixes the first-order request/outcome codecs and the
kernel projections for one concrete ZK, MPC, or FHE declaration.  The mode is
retained in `privateDeclaration`; no cross-mode coercion is introduced. -/
structure Adapter
    {S : CellState.Schema.{u, v, w, x}}
    (Nullifier : Type y) where
  requestContext : EffectRequestContext
  requestDigestBytes : List UInt8 → Digest
  requestCodec : LawfulCodec privateDeclaration.Request
  outcomeCodec : LawfulCodec privateDeclaration.Outcome
  effectDigest : privateDeclaration.Request → Digest
  patch : (request : privateDeclaration.Request) →
    privateDeclaration.Outcome → CellState.Patch S Digest
  nullifier : (request : privateDeclaration.Request) →
    privateDeclaration.Outcome → Option Nullifier

/-- Kernel projections for computation-only outcomes.  This is deliberately a
separate adapter from the release-capable one: sealed acceptance must not ask
an application to manufacture a release-bearing `Outcome`. -/
structure ComputationAdapter
    {S : CellState.Schema.{u, v, w, x}}
    (Nullifier : Type y) where
  requestContext : EffectRequestContext
  requestDigestBytes : List UInt8 → Digest
  requestCodec : LawfulCodec privateDeclaration.Request
  outcomeCodec : LawfulCodec privateDeclaration.ComputationOutcome
  effectDigest : privateDeclaration.Request → Digest
  patch : (request : privateDeclaration.Request) →
    privateDeclaration.ComputationOutcome → CellState.Patch S Digest
  nullifier : (request : privateDeclaration.Request) →
    privateDeclaration.ComputationOutcome → Option Nullifier

/-- Private disclosure decisions must match the legacy outcome's declared
effect.  Sealing is always safe; it emits no release even when release evidence
exists. -/
def DisclosureAllowed
    [DecidableEq Release]
    {request : privateDeclaration.Request}
    {outcome : privateDeclaration.Outcome} :
    DisclosureDecision Release DeclassificationAuthority
      (fun release => privateDeclaration.disclosureDeclaration.VerifiedRelease
        request.disclosureRequest outcome.output release) → Prop
  | .sealed => True
  | .reveal release _ => outcome.disclosureEffect = .reveal release
  | .declassify authority release _ =>
      outcome.disclosureEffect = .declassify authority release

/-- The semantic-effect-family instance shared by witness-ZK, shared-MPC, and
encrypted-RNS/FHE modes.  Existing private completion is its exact mode
evidence; the kernel patch remains a separate, validated semantic projection. -/
def family
    {S : CellState.Schema.{u, v, w, x}} {M : CellState.Materializer S Digest}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {Nullifier : Type y} [DecidableEq Release]
    (adapter : Adapter (S := S) privateDeclaration Nullifier)
    (pre : CellState.Materialized M) :
    SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier where
  Declaration := privateDeclaration.Request
  declarationCodec := adapter.requestCodec
  pre := pre
  request := fun request => ⟨adapter.requestContext.kind,
    adapter.requestContext.request
      (adapter.requestDigestBytes (adapter.requestCodec.encode request))
      (adapter.effectDigest request) pre.root⟩
  Outcome := fun _ => privateDeclaration.Outcome
  outcomeCodec := fun _ => adapter.outcomeCodec
  ModeEvidence := fun request outcome => privateDeclaration.Completion request outcome
  Postcondition := fun request outcome post =>
    (adapter.patch request outcome).ResultAt pre.logical post
  effectDigest := adapter.effectDigest
  patch := adapter.patch
  nullifier := adapter.nullifier
  Release := fun _ _ => Release
  DeclassificationAuthority := fun _ _ => DeclassificationAuthority
  ReleaseAuthorization := fun request outcome release =>
    privateDeclaration.disclosureDeclaration.VerifiedRelease
      request.disclosureRequest outcome.output release
  DisclosureAllowed := fun request outcome =>
    DisclosureAllowed privateDeclaration (request := request) (outcome := outcome)

/-- The sealed-only semantic family.  Its mode evidence is computation
completion, not release completion.  Both release carriers are empty, making a
reveal or declassification constructor uninhabited at this semantic boundary. -/
def sealedFamily
    {S : CellState.Schema.{u, v, w, x}} {M : CellState.Materializer S Digest}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {Nullifier : Type y}
    (adapter : ComputationAdapter (S := S) privateDeclaration Nullifier)
    (pre : CellState.Materialized M) :
    SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier where
  Declaration := privateDeclaration.Request
  declarationCodec := adapter.requestCodec
  pre := pre
  request := fun request => ⟨adapter.requestContext.kind,
    adapter.requestContext.request
      (adapter.requestDigestBytes (adapter.requestCodec.encode request))
      (adapter.effectDigest request) pre.root⟩
  Outcome := fun _ => privateDeclaration.ComputationOutcome
  outcomeCodec := fun _ => adapter.outcomeCodec
  ModeEvidence := fun request outcome =>
    privateDeclaration.ComputationCompletion request outcome
  Postcondition := fun request outcome post =>
    (adapter.patch request outcome).ResultAt pre.logical post
  effectDigest := adapter.effectDigest
  patch := adapter.patch
  nullifier := adapter.nullifier
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => nomatch release
  DisclosureAllowed := fun _ _ disclosure =>
    match disclosure with
    | .sealed => True
    | .reveal release _ => nomatch release
    | .declassify authority _ _ => nomatch authority

/-- The sealed family has no release value to authorize or disclose. -/
theorem sealedFamily_no_release
    {S : CellState.Schema.{u, v, w, x}} {M : CellState.Materializer S Digest}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {Nullifier : Type y}
    {pre : CellState.Materialized M}
    (adapter : ComputationAdapter (S := S) privateDeclaration Nullifier)
    (request : privateDeclaration.Request)
    (outcome : privateDeclaration.ComputationOutcome)
    (release : (sealedFamily (M := M) privateDeclaration adapter pre).Release
      request outcome) : False :=
  nomatch release

/-- The release decision already established by a private completion.  This is
only a projection of its request-indexed `VerifiedRelease`; it creates no new
cryptographic or privacy claim. -/
def disclosureOfCompletion
    [DecidableEq Release]
    {request : privateDeclaration.Request} {outcome : privateDeclaration.Outcome}
    (completion : privateDeclaration.Completion request outcome) :
    DisclosureDecision Release DeclassificationAuthority
      (fun release => privateDeclaration.disclosureDeclaration.VerifiedRelease
        request.disclosureRequest outcome.output release) :=
  match request.disclosureIntent with
  | .reveal => .reveal outcome.release completion.outputDisclosure
  | .declassify authority =>
      .declassify authority outcome.release completion.outputDisclosure

theorem disclosureOfCompletion_allowed
    [DecidableEq Release]
    {request : privateDeclaration.Request} {outcome : privateDeclaration.Outcome}
    (completion : privateDeclaration.Completion request outcome) :
    DisclosureAllowed privateDeclaration
      (disclosureOfCompletion privateDeclaration completion) := by
  cases intent : request.disclosureIntent with
  | reveal =>
      simpa [disclosureOfCompletion, intent, DisclosureAllowed,
        DisclosureIntent.materialize] using completion.disclosureDeclared
  | declassify authority =>
      simpa [disclosureOfCompletion, intent, DisclosureAllowed,
        DisclosureIntent.materialize] using completion.disclosureDeclared

/-- Join an existing mode-indexed private completion to the common kernel
authorization and canonical patch.  This is the first private positive path;
there is intentionally no adapter from a completion to a prior commit. -/
def acceptCompletion
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    [DecidableEq Release]
    (adapter : Adapter (S := S) privateDeclaration Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : privateDeclaration.Request} {outcome : privateDeclaration.Outcome}
    (authorization : Authorized portal authState commonRequest)
    (requestBound : (⟨kind, commonRequest⟩ : PackedEffectRequest) =
      (family privateDeclaration adapter pre).request request)
    (effectsDigestBound : commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : privateDeclaration.Completion request outcome)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request outcome)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (family (M := M) privateDeclaration adapter pre) commonRequest pre request outcome where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := effectsDigestBound
  preRootBound := preRootBound
  modeEvidence := completion
  validated := validated
  postcondition := validated.resultAt
  disclosure := disclosureOfCompletion privateDeclaration completion
  disclosureAllowed := disclosureOfCompletion_allowed privateDeclaration completion

/-- A completed private computation may also remain sealed.  Even here all
authorization, mode evidence, digest/root bindings, and the exact canonical
patch are still required; only the release projection is omitted. -/
def acceptCompletionSealed
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    [DecidableEq Release]
    (adapter : Adapter (S := S) privateDeclaration Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : privateDeclaration.Request} {outcome : privateDeclaration.Outcome}
    (authorization : Authorized portal authState commonRequest)
    (requestBound : (⟨kind, commonRequest⟩ : PackedEffectRequest) =
      (family privateDeclaration adapter pre).request request)
    (effectsDigestBound : commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : privateDeclaration.Completion request outcome)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request outcome)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (family (M := M) privateDeclaration adapter pre) commonRequest pre request outcome where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := effectsDigestBound
  preRootBound := preRootBound
  modeEvidence := completion
  validated := validated
  postcondition := validated.resultAt
  disclosure := .sealed
  disclosureAllowed := trivial

/-- Accept completed private computation without constructing, checking, or
retaining any release evidence.  The resulting family makes disclosure
uninhabited except for `.sealed`; a later reveal must be a separate authorized
effect. -/
def acceptComputationSealed
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (adapter : ComputationAdapter (S := S) privateDeclaration Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : privateDeclaration.Request}
    {outcome : privateDeclaration.ComputationOutcome}
    (authorization : Authorized portal authState commonRequest)
    (requestBound : (⟨kind, commonRequest⟩ : PackedEffectRequest) =
      (sealedFamily privateDeclaration adapter pre).request request)
    (effectsDigestBound : commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : privateDeclaration.ComputationCompletion request outcome)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request outcome)) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      (sealedFamily (M := M) privateDeclaration adapter pre)
      commonRequest pre request outcome where
  authorization := authorization
  preStateBound := rfl
  requestBound := requestBound
  effectsDigestBound := effectsDigestBound
  preRootBound := preRootBound
  modeEvidence := completion
  validated := validated
  postcondition := validated.resultAt
  disclosure := .sealed
  disclosureAllowed := trivial

/-- Private receipt evidence is reachable only through the common accepted
cell-effect token. -/
def receiptOfCompletion
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    [DecidableEq Release]
    (adapter : Adapter (S := S) privateDeclaration Nullifier)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : privateDeclaration.Request} {outcome : privateDeclaration.Outcome}
    (authorization : Authorized portal authState commonRequest)
    (requestBound : (⟨kind, commonRequest⟩ : PackedEffectRequest) =
      (family privateDeclaration adapter pre).request request)
    (effectsDigestBound : commonRequest.effectsDigest = adapter.effectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : privateDeclaration.Completion request outcome)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request outcome)) :
    ReceiptEvent (M := M) (family (M := M) privateDeclaration adapter pre) :=
  (acceptCompletion privateDeclaration adapter authorization requestBound effectsDigestBound
    preRootBound completion validated).toReceiptEvent

end PrivateCellEffect

end Minidregg.Theory
