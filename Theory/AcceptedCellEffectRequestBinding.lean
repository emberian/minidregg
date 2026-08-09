/-
# Theory.AcceptedCellEffectRequestBinding -- complete common-request binding

`AcceptedCellEffect` retains one exact `Authorized` token and binds the common
request's effect digest and pre-state root.  It intentionally does not choose
what `Request.argsDigest` means.  This module adds that missing family-generic
layer without changing the base token: each family selects one first-order
argument projection with a lawful codec, and `Bound` retains the original
accepted effect plus the one missing equality.

The digest projection is abstract.  No collision resistance or equality
reflection is claimed; clients which need reflection must supply the explicit
`BindingPremise` below.  The wrapper does not carry a second authorization
witness, patch, post-state, or declaration interpreter.
-/
import Theory.AcceptedCellEffect
import Theory.CredentialAuthorityEffects
import Theory.HyperdocumentOperations
import Theory.ReactiveCellTransition

namespace Minidregg.Theory.AcceptedCellEffectRequestBinding

open IndexedProgram
open TypedAuthorization

set_option autoImplicit false

universe u v w x y z

/-! ## One family-generic argument address -/

/-- A family-wide projection from a semantic declaration to the first-order
arguments named by the common request.  The projection is data, not an
interpreter: its target has one lawful codec and one selected digest operation.

The argument need not be the entire declaration.  Fields already represented
independently in `TypedAuthorization.Request` should not be redundantly forced
into `argsDigest`. -/
structure DeclarationAddressing
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier) where
  Argument : Type z
  argumentCodec : LawfulCodec Argument
  arguments : family.Declaration → Argument
  digestBytes : List UInt8 → Digest

/-- The common special case where the selected argument is the entire semantic
declaration.  This reuses the family's authoritative codec. -/
def wholeDeclarationAddressing
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier)
    (digestBytes : List UInt8 → Digest) : DeclarationAddressing family where
  Argument := family.Declaration
  argumentCodec := family.declarationCodec
  arguments := id
  digestBytes := digestBytes

def DeclarationAddressing.digest
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    (addressing : DeclarationAddressing family)
    (declaration : family.Declaration) : Digest :=
  addressing.digestBytes
    (addressing.argumentCodec.encode (addressing.arguments declaration))

@[simp] theorem DeclarationAddressing.digest_eq
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    (addressing : DeclarationAddressing family)
    (declaration : family.Declaration) :
    addressing.digest declaration =
      addressing.digestBytes
        (addressing.argumentCodec.encode (addressing.arguments declaration)) :=
  rfl

@[simp] theorem DeclarationAddressing.decode_arguments_encode
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    (addressing : DeclarationAddressing family)
    (declaration : family.Declaration) :
    addressing.argumentCodec.decode
      (addressing.argumentCodec.encode (addressing.arguments declaration)) =
        some (addressing.arguments declaration) :=
  addressing.argumentCodec.decode_encode (addressing.arguments declaration)

/-- Digest reflection is never inferred from a digest function.  It reflects
selected arguments, not entire declarations: a projection may intentionally
forget request-envelope fields which have their own common-request slots. -/
structure DeclarationAddressing.BindingPremise
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    (addressing : DeclarationAddressing family) : Prop where
  reflectsArgument : ∀ {left right : addressing.Argument},
    addressing.digestBytes (addressing.argumentCodec.encode left) =
        addressing.digestBytes (addressing.argumentCodec.encode right) →
      left = right

/-! ## Complete accepted request binding -/

/-- The original accepted effect is the sole authorization/transition token.
This wrapper adds only the declaration-derived argument equality missing from
the base structure. -/
structure Bound
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    (addressing : DeclarationAddressing family)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    (request : Request kind) (pre : CellState.Materialized M)
    (declaration : family.Declaration)
    (outcome : family.Outcome declaration) : Type (max u v w x y z) where
  accepted : AcceptedCellEffect (portal := portal) (authState := authState)
    family request pre declaration outcome
  argsDigestBound : request.argsDigest = addressing.digest declaration

def bind
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {addressing : DeclarationAddressing family}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration}
    {outcome : family.Outcome declaration}
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome)
    (argsDigestBound : request.argsDigest = addressing.digest declaration) :
    Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome :=
  ⟨accepted, argsDigestBound⟩

namespace Bound

variable
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {addressing : DeclarationAddressing family}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration}
    {outcome : family.Outcome declaration}

/-- The only authorization evidence is the one already retained by the nested
accepted effect. -/
def authorization
    (bound : Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :
    Authorized portal authState request :=
  bound.accepted.authorization

@[simp] theorem effectsDigest_exact
    (bound : Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :
    request.effectsDigest = family.effectDigest declaration :=
  bound.accepted.effectsDigestBound

@[simp] theorem preRoot_exact
    (bound : Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :
    request.preStateRoot = pre.root :=
  bound.accepted.preRootBound

omit [DecidableEq S.Field] [DecidableEq S.Resource] in
theorem argument_eq_of_same_digest
    (binding : addressing.BindingPremise)
    {left right : family.Declaration}
    (same : addressing.digest left = addressing.digest right) :
    addressing.arguments left = addressing.arguments right :=
  binding.reflectsArgument same

end Bound

/-- A mismatched common argument digest cannot be hidden by an otherwise valid
accepted effect. -/
theorem no_bound_of_args_mismatch
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {addressing : DeclarationAddressing family}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : family.Declaration}
    {outcome : family.Outcome declaration}
    (mismatch : request.argsDigest ≠ addressing.digest declaration) :
    IsEmpty (Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :=
  ⟨fun bound => mismatch bound.argsDigestBound⟩

/-! ## Existing private-computation wrapper is exactly this generic shape -/

def computationAddressing
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Relation BridgeName CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness OutputCommitment PrivateOutput ResourceEffect Footprint
      Nullifier ModeEvidencePins : Type z}
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : Minidregg.Theory.ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput ResourceEffect Footprint Nullifier
      ModeEvidencePins)
    (adapter : Minidregg.Theory.ComputationCellEffect.Adapter (S := S) declaration) :
    DeclarationAddressing
      (Minidregg.Theory.ComputationCellEffect.family (M := M) declaration adapter) :=
  wholeDeclarationAddressing
    (Minidregg.Theory.ComputationCellEffect.family (M := M) declaration adapter)
    adapter.requestDigestBytes

def ofComputationAccepted
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Relation BridgeName CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness OutputCommitment PrivateOutput ResourceEffect Footprint
      Nullifier ModeEvidencePins : Type z}
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (declaration : Minidregg.Theory.ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput ResourceEffect Footprint Nullifier
      ModeEvidencePins)
    (adapter : Minidregg.Theory.ComputationCellEffect.Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : declaration.Request} {result : declaration.Result}
    (accepted : Minidregg.Theory.ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) declaration adapter commonRequest pre request result) :
    Bound (portal := portal) (authState := authState)
      (computationAddressing (M := M) declaration adapter)
      commonRequest pre request result where
  accepted := accepted.cellEffect
  argsDigestBound := accepted.argsDigestBound

/-! ## Credential-authority family adapters

The four current credential acceptors bind effects and pre-state through
`AcceptedCellEffect`, but do not select an argument digest or retain its
equality.  Their adapters therefore require both pieces explicitly; this is a
real API residual, not a derivation hidden in this module. -/

def bindIssue
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (CredentialAuthorityEffects.IssueDeclaration kind)}
    {effectDigest : CredentialAuthorityEffects.IssueDeclaration kind → Digest}
    {declaration : CredentialAuthorityEffects.IssueDeclaration kind}
    (digestBytes : List UInt8 → Digest)
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.issueFamily domain pre codec effectDigest)
      request pre declaration ())
    (argsExact : request.argsDigest = digestBytes (codec.encode declaration)) :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.issueFamily domain pre codec effectDigest)
        digestBytes)
      request pre declaration () :=
  bind accepted argsExact

def bindAttenuation
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (CredentialAuthorityEffects.AttenuateDeclaration kind)}
    {parentCodec : LawfulCodec (CredentialAuthorityState.StoredCapability kind)}
    {effectDigest : CredentialAuthorityEffects.AttenuateDeclaration kind → Digest}
    {declaration : CredentialAuthorityEffects.AttenuateDeclaration kind}
    {parent : CredentialAuthorityState.StoredCapability kind}
    (digestBytes : List UInt8 → Digest)
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.attenuateFamily domain pre codec parentCodec
        effectDigest) request pre declaration parent)
    (argsExact : request.argsDigest = digestBytes (codec.encode declaration)) :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.attenuateFamily domain pre codec parentCodec
          effectDigest) digestBytes) request pre declaration parent :=
  bind accepted argsExact

def bindRevocation
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec CredentialAuthorityEffects.RevokeDeclaration}
    {effectDigest : CredentialAuthorityEffects.RevokeDeclaration → Digest}
    {declaration : CredentialAuthorityEffects.RevokeDeclaration}
    (digestBytes : List UInt8 → Digest)
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.revokeFamily domain pre codec effectDigest)
      request pre declaration ())
    (argsExact : request.argsDigest = digestBytes (codec.encode declaration)) :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.revokeFamily domain pre codec effectDigest)
        digestBytes)
      request pre declaration () :=
  bind accepted argsExact

def bindEpochRotation
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec CredentialAuthorityEffects.RotateEpochDeclaration}
    {effectDigest : CredentialAuthorityEffects.RotateEpochDeclaration → Digest}
    {declaration : CredentialAuthorityEffects.RotateEpochDeclaration}
    (digestBytes : List UInt8 → Digest)
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.rotateEpochFamily pre codec effectDigest)
      request pre declaration ())
    (argsExact : request.argsDigest = digestBytes (codec.encode declaration)) :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.rotateEpochFamily pre codec effectDigest)
        digestBytes)
      request pre declaration () :=
  bind accepted argsExact

/-! ## Hyperdocument staged-intent adapter -/

/-- Hyperdocument intentionally selects its acyclic `OperationIntent`, not its
request envelope, as the arguments named by `argsDigest`.  The digest projection
is exactly the existing domain-separated operation-id derivation. -/
def hyperdocumentAddressing
    {MDoc : Hyperdocument.Materializer Digest}
    (config : HyperdocumentOperations.Config) :
    DeclarationAddressing
      (HyperdocumentOperations.family (M := MDoc) config) where
  Argument := HyperdocumentOperationIntent.OperationIntent
  argumentCodec := config.intentAddressing.codec
  arguments := HyperdocumentOperations.Declaration.intent
  digestBytes := fun bytes =>
    (Hyperdocument.deriveIdentifier config.intentAddressing.derivation
      (⟨bytes⟩ : Hyperdocument.IdPreimage .v1 .operationIntent)).digest

@[simp] theorem hyperdocumentAddressing_digest
    {MDoc : Hyperdocument.Materializer Digest}
    (config : HyperdocumentOperations.Config)
    (declaration : HyperdocumentOperations.Declaration) :
    (hyperdocumentAddressing (MDoc := MDoc) config).digest declaration =
      (declaration.operationId config).digest :=
  rfl

/-- The current Hyperdocument accepted wrapper closes the generic binding
without an added premise: its common request already names the selected staged
intent through the canonical operation id. -/
def bindHyperdocument
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : HyperdocumentOperations.Declaration}
    (accepted : HyperdocumentOperations.Accepted config projection authorityPre
      documentPre portal declaration) :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState projection authorityPre)
      (hyperdocumentAddressing (MDoc := MDoc) config)
      (declaration.toRequest config) documentPre declaration () :=
  bind accepted.accepted rfl

/-- Load-bearing audit tooth: every generic Hyperdocument binding exposes the
same staged operation-id equality retained by its common request. -/
theorem hyperdocument_args_name_operation_intent
    {MDoc : Hyperdocument.Materializer Digest}
    {config : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState}
    {documentPre : Hyperdocument.Cell MDoc}
    {declaration : HyperdocumentOperations.Declaration}
    (bound : Bound (portal := portal) (authState := authState)
      (hyperdocumentAddressing (MDoc := MDoc) config)
      (declaration.toRequest config) documentPre declaration ()) :
    (declaration.toRequest config).argsDigest =
      (declaration.operationId config).digest := by
  simpa using bound.argsDigestBound

/-! ## Reactive residual

`ReactiveCellTransition.Accepted` is not an `AcceptedCellEffect`: its root is an
arbitrary `T.Root`, its request is `ReactiveController.Request`, and it retains
neither a `TypedAuthorization.Request` nor an `Authorized` token or a
`SemanticEffectFamily` declaration codec.  Consequently no honest adapter can
be defined here.  Closing that seam requires a separate Lean-authored carrier
identification and common-request construction; accepting callbacks here would
be a second interpreter, so this module intentionally provides none. -/

#print axioms Bound.effectsDigest_exact
#print axioms Bound.preRoot_exact
#print axioms no_bound_of_args_mismatch
#print axioms ofComputationAccepted
#print axioms bindIssue
#print axioms bindHyperdocument
#print axioms hyperdocument_args_name_operation_intent

end Minidregg.Theory.AcceptedCellEffectRequestBinding
