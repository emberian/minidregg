/-
# Theory.AcceptedCellEffectRequestBinding -- source argument projections

The complete request and exact canonical pre-state are mandatory fields of
`AcceptedCellEffect`. This module identifies the first-order source represented
by the family's already-bound `argsDigest`; it no longer introduces a stronger
optional admission wrapper. `Bound` is an abbreviation for the existing token.
Every `DeclarationAddressing` must prove its source projection is the argument
address already selected by the family. Digest reflection remains an explicit
pair-scoped premise and is never inferred from request equality.
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
  argsDigestExact : ∀ declaration,
    (family.request declaration).2.argsDigest =
      digestBytes (argumentCodec.encode (arguments declaration))

/-- The common special case where the selected argument is the entire semantic
declaration.  This reuses the family's authoritative codec. -/
def wholeDeclarationAddressing
    {S : CellState.Schema.{u, v, w, x}}
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier)
    (digestBytes : List UInt8 → Digest)
    (exact : ∀ declaration, (family.request declaration).2.argsDigest =
      digestBytes (family.declarationCodec.encode declaration)) : DeclarationAddressing family where
  Argument := family.Declaration
  argumentCodec := family.declarationCodec
  arguments := id
  digestBytes := digestBytes
  argsDigestExact := exact

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
    (addressing : DeclarationAddressing family)
    (left right : addressing.Argument) : Prop where
  reflectsArgument : addressing.digestBytes (addressing.argumentCodec.encode left) =
        addressing.digestBytes (addressing.argumentCodec.encode right) →
      left = right

/-! ## Complete accepted request binding -/

/-- There is one admission token. The addressing argument is checked source
metadata, not an additional acceptance gate or a wrapper that callers can drop. -/
abbrev Bound
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    (_addressing : DeclarationAddressing family)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    (request : Request kind) (pre : CellState.Materialized M)
    (declaration : family.Declaration)
    (outcome : family.Outcome declaration) : Type (max u v w x y z) :=
  AcceptedCellEffect (portal := portal) (authState := authState)
    family request pre declaration outcome

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

/-- Argument equality is forced by the base token and the source projection. -/
theorem argsDigestBound
    (bound : Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :
    request.argsDigest = addressing.digest declaration :=
  bound.request_argsDigest_exact.trans (addressing.argsDigestExact declaration)

@[simp] theorem effectsDigest_exact
    (bound : Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :
    request.effectsDigest = family.effectDigest declaration :=
  bound.effectsDigestBound

@[simp] theorem preRoot_exact
    (bound : Bound (portal := portal) (authState := authState)
      addressing request pre declaration outcome) :
    request.preStateRoot = pre.root :=
  bound.preRootBound

omit [DecidableEq S.Field] [DecidableEq S.Resource] in
theorem argument_eq_of_same_digest
    {left right : family.Declaration}
    (binding : addressing.BindingPremise (addressing.arguments left)
      (addressing.arguments right))
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
  ⟨fun bound => mismatch (Bound.argsDigestBound bound)⟩

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
    (adapter : Minidregg.Theory.ComputationCellEffect.Adapter (S := S) declaration)
    (pre : CellState.Materialized M) :
    DeclarationAddressing
      (Minidregg.Theory.ComputationCellEffect.family (M := M) declaration adapter pre) :=
  wholeDeclarationAddressing
    (Minidregg.Theory.ComputationCellEffect.family (M := M) declaration adapter pre)
    adapter.requestDigestBytes (fun _ => rfl)

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
      (computationAddressing (M := M) declaration adapter pre)
      commonRequest pre request result :=
  accepted.cellEffect

/-! ## Credential-authority source projections

All four families now select the codec/digest operation and exact request as
part of their trusted source. No per-token `argsExact` premise is needed.
-/

def bindIssue
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec (CredentialAuthorityEffects.IssueDeclaration kind)}
    {effectDigest : CredentialAuthorityEffects.IssueDeclaration kind → Digest}
    {declaration : CredentialAuthorityEffects.IssueDeclaration kind}
    {context : CredentialAuthorityEffects.RequestContext}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.issueFamily domain pre codec effectDigest context)
      request pre declaration ())
    :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.issueFamily domain pre codec effectDigest context)
        context.argsDigestBytes (fun _ => rfl))
      request pre declaration () :=
  accepted

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
    {context : CredentialAuthorityEffects.RequestContext}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.attenuateFamily domain pre codec parentCodec
        effectDigest context) request pre declaration parent)
    :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.attenuateFamily domain pre codec parentCodec
          effectDigest context) context.argsDigestBytes (fun _ => rfl)) request pre declaration parent :=
  accepted

def bindRevocation
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec CredentialAuthorityEffects.RevokeDeclaration}
    {effectDigest : CredentialAuthorityEffects.RevokeDeclaration → Digest}
    {declaration : CredentialAuthorityEffects.RevokeDeclaration}
    {context : CredentialAuthorityEffects.RequestContext}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.revokeFamily domain pre codec effectDigest context)
      request pre declaration ())
    :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.revokeFamily domain pre codec effectDigest context)
        context.argsDigestBytes (fun _ => rfl))
      request pre declaration () :=
  accepted

def bindEpochRotation
    {M : CredentialAuthorityState.Materializer}
    {domain : CredentialAuthorityState.ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M}
    {portal : Portal} {kind : ResourceKind} {request : Request kind}
    {codec : LawfulCodec CredentialAuthorityEffects.RotateEpochDeclaration}
    {effectDigest : CredentialAuthorityEffects.RotateEpochDeclaration → Digest}
    {declaration : CredentialAuthorityEffects.RotateEpochDeclaration}
    {context : CredentialAuthorityEffects.RequestContext}
    (accepted : AcceptedCellEffect (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (CredentialAuthorityEffects.rotateEpochFamily pre codec effectDigest context)
      request pre declaration ())
    :
    Bound (portal := portal)
      (authState := CredentialAuthorityState.authState domain pre)
      (wholeDeclarationAddressing
        (CredentialAuthorityEffects.rotateEpochFamily pre codec effectDigest context)
        context.argsDigestBytes (fun _ => rfl))
      request pre declaration () :=
  accepted

/-! ## Hyperdocument staged-intent adapter -/

/-- Hyperdocument intentionally selects its acyclic `OperationIntent`, not its
request envelope, as the arguments named by `argsDigest`.  The digest projection
is exactly the existing domain-separated operation-id derivation. -/
def hyperdocumentAddressing
    {MDoc : Hyperdocument.Materializer Digest}
    (config : HyperdocumentOperations.Config) (pre : Hyperdocument.Cell MDoc) :
    DeclarationAddressing
      (HyperdocumentOperations.family (M := MDoc) config pre) where
  Argument := HyperdocumentOperationIntent.OperationIntent
  argumentCodec := config.intentAddressing.codec
  arguments := HyperdocumentOperations.Declaration.intent
  digestBytes := fun bytes =>
    (Hyperdocument.deriveIdentifier config.intentAddressing.derivation
      (⟨bytes⟩ : Hyperdocument.IdPreimage .v1 .operationIntent)).digest
  argsDigestExact := fun _ => rfl

@[simp] theorem hyperdocumentAddressing_digest
    {MDoc : Hyperdocument.Materializer Digest}
    (config : HyperdocumentOperations.Config) (pre : Hyperdocument.Cell MDoc)
    (declaration : HyperdocumentOperations.Declaration) :
    (hyperdocumentAddressing (MDoc := MDoc) config pre).digest declaration =
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
      (hyperdocumentAddressing (MDoc := MDoc) config documentPre)
      (declaration.toRequest config) documentPre declaration () :=
  accepted.accepted

/-- Load-bearing audit tooth: every generic Hyperdocument binding exposes the
same staged operation-id equality retained by its common request. -/
theorem hyperdocument_args_name_operation_intent
    {MDoc : Hyperdocument.Materializer Digest}
    {config : HyperdocumentOperations.Config}
    {portal : Portal} {authState : AuthState}
    {documentPre : Hyperdocument.Cell MDoc}
    {declaration : HyperdocumentOperations.Declaration}
    (bound : Bound (portal := portal) (authState := authState)
      (hyperdocumentAddressing (MDoc := MDoc) config documentPre)
      (declaration.toRequest config) documentPre declaration ()) :
    (declaration.toRequest config).argsDigest =
      (declaration.operationId config).digest := by
  simpa using (Bound.argsDigestBound bound)

/-! ## Reactive residual

`ReactiveCellTransition.Accepted` is not an `AcceptedCellEffect`: its root is an
arbitrary `T.Root`, its request is `ReactiveController.Request`, and it retains
neither a `TypedAuthorization.Request` nor an `Authorized` token or a
`SemanticEffectFamily` declaration codec.  Consequently no honest adapter can
be defined here.  Closing that seam requires a separate Lean-authored carrier
identification and common-request construction; accepting callbacks here would
be a second interpreter, so this module intentionally provides none. -/

/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.Bound.effectsDigest_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Bound.effectsDigest_exact
/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.Bound.preRoot_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Bound.preRoot_exact
/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.no_bound_of_args_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_bound_of_args_mismatch
/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.ofComputationAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofComputationAccepted
/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.bindIssue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bindIssue
/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.bindHyperdocument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bindHyperdocument
/-- info: 'Minidregg.Theory.AcceptedCellEffectRequestBinding.hyperdocument_args_name_operation_intent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyperdocument_args_name_operation_intent

end Minidregg.Theory.AcceptedCellEffectRequestBinding
