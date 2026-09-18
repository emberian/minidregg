/-
# Kernel.MultiCellHyperedge -- incidence-indexed heterogeneous cell turns

`Kernel.TypedCellHyperedge` composes several accepted effects over one common
cell.  That is useful for same-cell patch fusion, but it is not a multi-cell
turn.  This module removes that restriction: every incidence chooses its own
schema, materializer, canonical pre-cell, authorization projection, and
accepted semantic-effect family.  The only shared data are the turn header,
the joint receipt binding, and the resource equation.

The declaration is data-first.  It contains no accepted-effect token.  A
commit is indexed by a complete family of `AcceptedCellEffect`s, one for every
incidence, and therefore cannot be exposed after only a prefix validates.
Physical compare-and-swap across databases, receipt persistence, cryptographic
binding, consensus, and retry policy remain in the explicit `HandlerBoundary`.
The boundary may return evidence, but it cannot alter the Lean-owned exact
pre/post cells, requests, authority projections, cell identities, or balance
equation.
-/
import Kernel.Turn
import Theory.AcceptedCellEffect
import Theory.PolicyInstall
import Mathlib.Algebra.Group.ULift

namespace Minidregg.Kernel.MultiCellHyperedge

open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z b h

/-! ## Incidence-indexed cells and data-first legs -/

/-- The heterogeneous cells participating in one turn.  Decidable equality is
stored per schema instead of postulating one universe-wide erased key type. -/
structure CellFamily (Incidence : Type z) where
  schema : Incidence -> CellState.Schema.{u, v, w, x}
  fieldDecidableEq : (incidence : Incidence) ->
    DecidableEq (schema incidence).Field
  resourceDecidableEq : (incidence : Incidence) ->
    DecidableEq (schema incidence).Resource
  materializer : (incidence : Incidence) ->
    CellState.Materializer (schema incidence) Digest
  portal : Incidence -> Portal
  projectAuthority : (incidence : Incidence) ->
    CellState.LogicalState (schema incidence) -> AuthState
  cellId : Incidence -> Digest

/-- The physical and semantic cell layout before any policy portal has been
constructed. This is the portal-independent part of the existing `CellFamily`,
so preparing policy inputs never needs a placeholder authorization portal. -/
structure CellLayout (Incidence : Type z) where
  schema : Incidence -> CellState.Schema.{u, v, w, x}
  fieldDecidableEq : (incidence : Incidence) ->
    DecidableEq (schema incidence).Field
  resourceDecidableEq : (incidence : Incidence) ->
    DecidableEq (schema incidence).Resource
  materializer : (incidence : Incidence) ->
    CellState.Materializer (schema incidence) Digest
  projectAuthority : (incidence : Incidence) ->
    CellState.LogicalState (schema incidence) -> AuthState
  cellId : Incidence -> Digest

/-- Policy construction supplies only the portals; it cannot replace the
layout, authority projections, or physical cell identities it evaluated. -/
def CellLayout.withPortals {Incidence : Type z}
    (layout : CellLayout.{u, v, w, x, z} Incidence) (portals : Incidence -> Portal) :
    CellFamily.{u, v, w, x, z} Incidence where
  schema := layout.schema
  fieldDecidableEq := layout.fieldDecidableEq
  resourceDecidableEq := layout.resourceDecidableEq
  materializer := layout.materializer
  projectAuthority := layout.projectAuthority
  cellId := layout.cellId
  portal := portals

local instance layoutFieldDecidableEq
    {Incidence : Type z} (layout : CellLayout.{u, v, w, x, z} Incidence)
    (incidence : Incidence) : DecidableEq (layout.schema incidence).Field :=
  layout.fieldDecidableEq incidence

local instance layoutResourceDecidableEq
    {Incidence : Type z} (layout : CellLayout.{u, v, w, x, z} Incidence)
    (incidence : Incidence) : DecidableEq (layout.schema incidence).Resource :=
  layout.resourceDecidableEq incidence

/-- Raw source data for one final per-cell patch. It contains neither a
semantic family nor a portal: some families mention authorization in their
mode-evidence type, so even selecting those families must be deferred. -/
structure CandidateLegData
    {Incidence : Type z} (layout : CellLayout.{u, v, w, x, z} Incidence)
    (incidence : Incidence) where
  pre : CellState.Materialized (layout.materializer incidence)
  patch : CellState.Patch (layout.schema incidence) Digest
  request : PackedEffectRequest
  Postcondition : CellState.LogicalState (layout.schema incidence) -> Prop

/-- A source-owned late interpretation of one already-prepared raw leg. Every
pure facet agrees exactly with the prepared source; choosing a real policy
portal may change evidence types, never the state, request, patch, or result
relation that policy evaluation already consumed. -/
structure SemanticLegBinding
    {Incidence : Type z} {layout : CellLayout.{u, v, w, x, z} Incidence}
    {incidence : Incidence} (raw : CandidateLegData layout incidence) :
    Type (max u v w x (y + 1) (z + 1)) where
  Nullifier : Type y
  family : SemanticEffectFamily.{u, v, w, x, y, z}
    (layout.schema incidence) (layout.materializer incidence) Nullifier
  declaration : family.Declaration
  outcome : family.Outcome declaration
  preExact : raw.pre = family.pre
  requestExact : raw.request = family.request declaration
  effectsExact : raw.request.2.effectsDigest = family.effectDigest declaration
  patchExact : family.patch declaration outcome = raw.patch
  postconditionExact : forall post,
    family.Postcondition declaration outcome post ↔ raw.Postcondition post

/-- A receiving module fixes this plan in code. The complete descriptor
derives each raw leg and its later semantic interpretation. These functions
and the state projection are never decoded from an incoming request. -/
structure PreparationPlan
    {Incidence : Type z} (layout : CellLayout.{u, v, w, x, z} Incidence)
    (Source : Type z) where
  leg : Source -> (incidence : Incidence) -> CandidateLegData layout incidence
  /-- Concrete plans commit canonical full source coordinates, including
  domain, semantics, nonce and relevant expected-state identities. -/
  jointDigest : Source -> Digest
  /-- Native effects remain distinct; the full descriptor derives every one. -/
  legEffectsDigest : Source -> Incidence -> Digest
  bindFamily : (source : Source) -> (portals : Incidence -> Portal) ->
    (incidence : Incidence) ->
      SemanticLegBinding.{u, v, w, x, y, z} (leg source incidence)

/-- One complete source-derived raw tuple before any portal, authorization, or
mode evidence exists. Its posts are the existing canonical patch interpreter's
results. Distinct physical cells each have one final patch; a source combines
its sequential operations before entering this tuple. -/
structure PreparedTuple
    {Incidence : Type z} {layout : CellLayout.{u, v, w, x, z} Incidence}
    {Source : Type z} (plan : PreparationPlan.{u, v, w, x, y, z} layout Source) where
  source : Source
  primary : Incidence
  validated : (incidence : Incidence) ->
    CellState.ValidatedPatch (layout.materializer incidence)
      (plan.leg source incidence).pre (plan.leg source incidence).patch
  postconditions : forall incidence,
    (plan.leg source incidence).Postcondition (validated incidence).apply.logical
  cellIdsDistinct : Function.Injective layout.cellId
  requestRoots : forall incidence,
    (plan.leg source incidence).request.2.preStateRoot =
      (plan.leg source incidence).pre.root
  requestEffects : forall incidence,
    (plan.leg source incidence).request.2.effectsDigest =
      plan.legEffectsDigest source incidence

namespace PreparedTuple

variable {Incidence : Type z} {layout : CellLayout.{u, v, w, x, z} Incidence}
    {Source : Type z} {plan : PreparationPlan.{u, v, w, x, y, z} layout Source}

def pre (prepared : PreparedTuple plan) (incidence : Incidence) :
    CellState.Materialized (layout.materializer incidence) :=
  (plan.leg prepared.source incidence).pre

def post (prepared : PreparedTuple plan) (incidence : Incidence) :
    CellState.Materialized (layout.materializer incidence) :=
  (prepared.validated incidence).apply

def logicalPre (prepared : PreparedTuple plan) (incidence : Incidence) :
    CellState.LogicalState (layout.schema incidence) :=
  (prepared.pre incidence).logical

def logicalPost (prepared : PreparedTuple plan) (incidence : Incidence) :
    CellState.LogicalState (layout.schema incidence) :=
  (prepared.post incidence).logical

def request (prepared : PreparedTuple plan) (incidence : Incidence) :
    PackedEffectRequest :=
  (plan.leg prepared.source incidence).request

theorem post_exact (prepared : PreparedTuple plan) (incidence : Incidence) :
    prepared.post incidence = (prepared.validated incidence).apply := rfl

theorem local_postcondition (prepared : PreparedTuple plan) (incidence : Incidence) :
    (plan.leg prepared.source incidence).Postcondition (prepared.post incidence).logical :=
  prepared.postconditions incidence

end PreparedTuple

/-- Recover each schema's equality procedures only when that exact incidence
is in scope.  These are projections of declaration data, not global axioms. -/
local instance cellFieldDecidableEq
    {Incidence : Type z} (cells : CellFamily.{u, v, w, x, z} Incidence)
    (incidence : Incidence) : DecidableEq (cells.schema incidence).Field :=
  cells.fieldDecidableEq incidence

local instance cellResourceDecidableEq
    {Incidence : Type z} (cells : CellFamily.{u, v, w, x, z} Incidence)
    (incidence : Incidence) : DecidableEq (cells.schema incidence).Resource :=
  cells.resourceDecidableEq incidence

/-- One raw semantic leg.  This is deliberately not accepted yet: declaration
data may be decoded and inspected without manufacturing semantic admission. -/
structure LegData
    {Incidence : Type z} (cells : CellFamily.{u, v, w, x, z} Incidence)
    (incidence : Incidence) : Type (max u v w x (y + 1) (z + 1)) where
  Nullifier : Type y
  family : SemanticEffectFamily.{u, v, w, x, y, z}
    (cells.schema incidence) (cells.materializer incidence) Nullifier
  kind : ResourceKind
  request : Request kind
  declaration : family.Declaration
  outcome : family.Outcome declaration

/-- One shared logical turn header.  It is not a Mina call forest: every leg
is a sibling incidence of this one header. -/
structure Header where
  domain : Digest
  turnId : Digest
  apex : Digest
  deriving DecidableEq, Repr

/-- Candidate data for one heterogeneous turn.  Each pre-cell is canonical
under its own materializer; no post-cell or authorization witness is supplied. -/
structure Declaration
    {Incidence : Type z} (cells : CellFamily.{u, v, w, x, z} Incidence) where
  header : Header
  pre : (incidence : Incidence) ->
    CellState.Materialized (cells.materializer incidence)
  legs : (incidence : Incidence) -> LegData.{u, v, w, x, y, z} cells incidence

namespace Declaration

variable {Incidence : Type z}
variable {cells : CellFamily.{u, v, w, x, z} Incidence}
variable (declaration : Declaration.{u, v, w, x, y, z} cells)

/-- The exact accepted-effect proposition for one incidence.  Its portal and
authorization state are definitionally projected from that incidence's exact
canonical pre-cell. -/
abbrev AcceptedLeg (incidence : Incidence) : Type _ :=
  @AcceptedCellEffect.{u, v, w, x, y, z}
    (cells.schema incidence)
    (cells.fieldDecidableEq incidence)
    (cells.resourceDecidableEq incidence)
    (cells.materializer incidence)
    (declaration.legs incidence).Nullifier
    (declaration.legs incidence).family
    (cells.portal incidence)
    (cells.projectAuthority incidence (declaration.pre incidence).logical)
    (declaration.legs incidence).kind
    (declaration.legs incidence).request
    (declaration.pre incidence)
    (declaration.legs incidence).declaration
    (declaration.legs incidence).outcome

/-- Admission validates all incidences at once.  This dependent function is
the semantic all-legs barrier; a prefix of proofs has no coercion to it. -/
abbrev AcceptedLegs : Type _ :=
  (incidence : Incidence) -> declaration.AcceptedLeg incidence

@[simp] theorem accepted_request_preRoot
    (accepted : declaration.AcceptedLegs) (incidence : Incidence) :
    (declaration.legs incidence).request.preStateRoot =
      (declaration.pre incidence).root :=
  (accepted incidence).preRootBound

@[simp] theorem accepted_request_effectsDigest
    (accepted : declaration.AcceptedLegs) (incidence : Incidence) :
    (declaration.legs incidence).request.effectsDigest =
      (declaration.legs incidence).family.effectDigest
        (declaration.legs incidence).declaration :=
  (accepted incidence).effectsDigestBound

/-- The exact per-cell canonical post selected by its accepted typed patch. -/
def post (accepted : declaration.AcceptedLegs) (incidence : Incidence) :
    CellState.Materialized (cells.materializer incidence) :=
  (accepted incidence).prepared.post

@[simp] theorem post_exact
    (accepted : declaration.AcceptedLegs) (incidence : Incidence) :
    declaration.post accepted incidence = (accepted incidence).validated.apply :=
  rfl

/-- Request authority is retained at its exact heterogeneous incidence; it is
never collapsed to a Boolean or a common ambient authorization state. -/
def authorization (accepted : declaration.AcceptedLegs)
    (incidence : Incidence) :
    Authorized (cells.portal incidence)
      (cells.projectAuthority incidence (declaration.pre incidence).logical)
      (declaration.legs incidence).request :=
  (accepted incidence).authorization

end Declaration

/-! ## Authorize the already-prepared tuple without changing its post -/

namespace PreparedTuple

variable {Incidence : Type z} {layout : CellLayout.{u, v, w, x, z} Incidence}
    {Source : Type z} {plan : PreparationPlan.{u, v, w, x, y, z} layout Source}

def binding (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (incidence : Incidence) : SemanticLegBinding (plan.leg prepared.source incidence) :=
  plan.bindFamily prepared.source portals incidence

/-- The joint identity is the full descriptor commitment; native request
identities remain per-leg. Only the eventual apex is supplied at the existing
joint commitment boundary. -/
def header (prepared : PreparedTuple plan) (apex : Digest) : Header where
  domain := (prepared.request prepared.primary).2.domain
  turnId := plan.jointDigest prepared.source
  apex := apex

/-- Construct the existing declaration after real portals are selected. The
late source binding cannot choose different requests, patches or pre-cells. -/
def toDeclaration (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (apex : Digest) :
    Declaration.{u, v, w, x, y, z} (layout.withPortals portals) where
  header := prepared.header apex
  pre := prepared.pre
  legs := fun incidence =>
    { Nullifier := (prepared.binding portals incidence).Nullifier
      family := (prepared.binding portals incidence).family
      kind := (prepared.request incidence).1
      request := (prepared.request incidence).2
      declaration := (prepared.binding portals incidence).declaration
      outcome := (prepared.binding portals incidence).outcome }

/-- Transport the already-validated raw patch across the exact source binding.
There is no second patch executor or post-selection step. -/
def boundValidated (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (incidence : Incidence) :
    CellState.ValidatedPatch (layout.materializer incidence) (prepared.pre incidence)
      ((prepared.binding portals incidence).family.patch
        (prepared.binding portals incidence).declaration
        (prepared.binding portals incidence).outcome) := by
  simpa only [(prepared.binding portals incidence).patchExact] using
    prepared.validated incidence

theorem bound_post_exact (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (incidence : Incidence) :
    (prepared.boundValidated portals incidence).apply = prepared.post incidence := by
  apply CellState.Materialized.ext
  simp only [CellState.ValidatedPatch.apply, (prepared.binding portals incidence).patchExact]
  rfl

/-- All evidence deferred during raw preparation is mandatory at final
admission. In particular an authority-bearing mode is never replaced by an
empty witness merely to construct a policy context. -/
structure AdmissionEvidence (prepared : PreparedTuple plan) (portals : Incidence -> Portal) where
  modes : forall incidence,
    (prepared.binding portals incidence).family.ModeEvidence
      (prepared.binding portals incidence).declaration
      (prepared.binding portals incidence).outcome
  authorizations : forall incidence,
    Authorized (portals incidence)
      (layout.projectAuthority incidence (prepared.pre incidence).logical)
      (prepared.request incidence).2
  disclosure : (incidence : Incidence) ->
    DisclosureDecision
      ((prepared.binding portals incidence).family.Release
        (prepared.binding portals incidence).declaration
        (prepared.binding portals incidence).outcome)
      ((prepared.binding portals incidence).family.DeclassificationAuthority
        (prepared.binding portals incidence).declaration
        (prepared.binding portals incidence).outcome)
      ((prepared.binding portals incidence).family.ReleaseAuthorization
        (prepared.binding portals incidence).declaration
        (prepared.binding portals incidence).outcome)
  disclosureAllowed : forall incidence,
    (prepared.binding portals incidence).family.DisclosureAllowed
      (prepared.binding portals incidence).declaration
      (prepared.binding portals incidence).outcome (disclosure incidence)

/-- Add all exact source mode and authorization evidence to the one evaluated
raw tuple, producing the existing complete `AcceptedLegs` barrier. -/
def accept (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (apex : Digest) (evidence : prepared.AdmissionEvidence portals) :
    (prepared.toDeclaration portals apex).AcceptedLegs :=
  fun incidence =>
    { authorization := evidence.authorizations incidence
      preStateBound := (prepared.binding portals incidence).preExact
      requestBound := (prepared.binding portals incidence).requestExact
      effectsDigestBound := (prepared.binding portals incidence).effectsExact
      preRootBound := prepared.requestRoots incidence
      modeEvidence := evidence.modes incidence
      validated := prepared.boundValidated portals incidence
      postcondition := by
        apply ((prepared.binding portals incidence).postconditionExact _).mpr
        change (plan.leg prepared.source incidence).Postcondition
          (prepared.boundValidated portals incidence).apply.logical
        exact (congrArg
          (fun cell : CellState.Materialized (layout.materializer incidence) =>
            (plan.leg prepared.source incidence).Postcondition cell.logical)
          (prepared.bound_post_exact portals incidence)).mpr (prepared.postconditions incidence)
      disclosure := evidence.disclosure incidence
      disclosureAllowed := evidence.disclosureAllowed incidence }

/-- Every final accepted post is the raw post seen by policy before the real
portals or mode evidence existed. Exact patch equality, not hash reflection,
justifies this correspondence. -/
theorem accepted_posts_exact (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (apex : Digest) (evidence : prepared.AdmissionEvidence portals) (incidence : Incidence) :
    (prepared.toDeclaration portals apex).post
      (prepared.accept portals apex evidence) incidence = prepared.post incidence :=
  prepared.bound_post_exact portals incidence

theorem accepted_mode_exact (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (apex : Digest) (evidence : prepared.AdmissionEvidence portals) (incidence : Incidence) :
    (prepared.accept portals apex evidence incidence).modeEvidence = evidence.modes incidence := rfl

theorem declaration_pre_exact (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (apex : Digest) (incidence : Incidence) :
    (prepared.toDeclaration portals apex).pre incidence = prepared.pre incidence := rfl

theorem declaration_effects_exact (prepared : PreparedTuple plan) (portals : Incidence -> Portal)
    (apex : Digest) (incidence : Incidence) :
    ((prepared.toDeclaration portals apex).legs incidence).request.effectsDigest =
      plan.legEffectsDigest prepared.source incidence :=
  prepared.requestEffects incidence

theorem declaration_joint_identity_exact (prepared : PreparedTuple plan)
    (portals : Incidence -> Portal) (apex : Digest) :
    (prepared.toDeclaration portals apex).header.turnId = plan.jointDigest prepared.source := rfl

/-- The family declaration is computed from the retained full source by the
same fixed late plan, even if two external hashes were hypothetically equal. -/
theorem declaration_source_exact (prepared : PreparedTuple plan)
    (portals : Incidence -> Portal) (apex : Digest) (incidence : Incidence) :
    ((prepared.toDeclaration portals apex).legs incidence).declaration =
      (plan.bindFamily prepared.source portals incidence).declaration := rfl

theorem no_prepared_tuple_of_conflicting_cell
    (left right : Incidence) (different : left ≠ right)
    (sameCell : layout.cellId left = layout.cellId right) :
    IsEmpty (PreparedTuple plan) :=
  ⟨fun prepared => different (prepared.cellIdsDistinct sameCell)⟩

end PreparedTuple

/-! ## Joint receipt input and resource semantics -/

/-- The one handler-supplied joint binding input.  The joint commitment is
required below to equal the Lean header apex.  `receiptRoot` is retained as
data; no collision-resistance or persistence claim is invented here. -/
structure JointCommitInput where
  jointCommit : Digest
  receiptRoot : Digest
  deriving DecidableEq, Repr

/-- The physical/cryptographic boundary.  Its evidence family is indexed by
the exact declaration, complete accepted-leg family, and exact joint input.
Implementations may witness a database transaction or commitment opening here;
this kernel does not assert that they did so merely because a digest exists. -/
structure HandlerBoundary
    {Incidence : Type z} {cells : CellFamily.{u, v, w, x, z} Incidence}
    (declaration : Declaration.{u, v, w, x, y, z} cells) where
  Evidence : (accepted : declaration.AcceptedLegs) ->
    JointCommitInput -> Type h

/-- Cross-schema resource meaning is explicit.  The law sees the exact raw leg
and its exact accepted effect, so an implementation cannot charge a different
request or post-state under the same incidence. -/
structure ResourceLaw
    {Incidence : Type z} {cells : CellFamily.{u, v, w, x, z} Incidence}
    (declaration : Declaration.{u, v, w, x, y, z} cells)
    (Coordinate : Type y) (Balance : Type b) [AddCommMonoid Balance] where
  delta : (incidence : Incidence) -> declaration.AcceptedLeg incidence ->
    Coordinate -> Balance

variable {Incidence : Type z} [Fintype Incidence] [DecidableEq Incidence]
variable {cells : CellFamily.{u, v, w, x, z} Incidence}
variable {declaration : Declaration.{u, v, w, x, y, z} cells}
variable {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
variable (law : ResourceLaw.{u, v, w, x, y, z, b} declaration Coordinate Balance)

/-- The exact joint balance vector of a complete accepted family. -/
def aggregateDelta (accepted : declaration.AcceptedLegs) : Coordinate -> Balance :=
  fun coordinate => Finset.univ.sum fun incidence =>
    law.delta incidence (accepted incidence) coordinate

/-- Heterogeneous eager nullifiers retain their incidence and dependent type. -/
def JointNullifier (accepted : declaration.AcceptedLegs) : Type _ :=
  Sigma fun incidence => (declaration.legs incidence).Nullifier

noncomputable def jointNullifiers (accepted : declaration.AcceptedLegs) :
    List (JointNullifier accepted) :=
  Finset.univ.toList.filterMap fun incidence =>
    match (declaration.legs incidence).family.nullifier
      (declaration.legs incidence).declaration
      (declaration.legs incidence).outcome with
    | none => none
    | some nullifier => some ⟨incidence, nullifier⟩

/-! ## Proof-relevant admission -/

/-- A commit exists only after every incidence has an accepted semantic effect.
Cell identities are distinct, every request shares the declared domain, the
resource vector balances, and the handler evidence binds the one exact joint
input to this complete accepted family. -/
structure Commit
    (accepted : declaration.AcceptedLegs)
    (boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration) :
    Type (max u v w x y z b h) where
  cellIdsDistinct : Function.Injective cells.cellId
  sharedDomain : forall incidence,
    (declaration.legs incidence).request.domain = declaration.header.domain
  aggregateBalanced : aggregateDelta law accepted = 0
  jointInput : JointCommitInput
  jointCommitExact : jointInput.jointCommit = declaration.header.apex
  jointEvidence : boundary.Evidence accepted jointInput

/-- Existentially package the complete family with its joint commit. -/
def AdmittedCommit
    (boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration) : Type _ :=
  Sigma fun accepted => Commit law accepted boundary

namespace Commit

variable {law : ResourceLaw.{u, v, w, x, y, z, b} declaration Coordinate Balance}
variable {accepted : declaration.AcceptedLegs}
variable {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}

def post (commit : Commit law accepted boundary) (incidence : Incidence) :
    CellState.Materialized (cells.materializer incidence) :=
  declaration.post accepted incidence

@[simp] theorem post_exact (commit : Commit law accepted boundary)
    (incidence : Incidence) :
    commit.post incidence = (accepted incidence).validated.apply :=
  rfl

def legAuthorization (commit : Commit law accepted boundary)
    (incidence : Incidence) :
    Authorized (cells.portal incidence)
      (cells.projectAuthority incidence (declaration.pre incidence).logical)
      (declaration.legs incidence).request :=
  declaration.authorization accepted incidence

noncomputable def nullifiers (commit : Commit law accepted boundary) :
    List (JointNullifier accepted) :=
  jointNullifiers accepted

/-! ### Projection to the abstract wide pullback -/

/-- A dependent carrier keeps each heterogeneous cell in its own schema while
retaining the joint apex installed by the logical step. -/
structure Carrier where
  incidence : Incidence
  state : CellState.Materialized (cells.materializer incidence)
  jointApex : Digest

def step (state : Carrier (cells := cells))
    (turn : Commit law accepted boundary) : Carrier (cells := cells) where
  incidence := state.incidence
  state := turn.post state.incidence
  jointApex := declaration.header.apex

def turnId (_incidence : Incidence) (state : Carrier (cells := cells)) : Digest :=
  state.jointApex

def halfEdge (incidence : Incidence) (_state : Carrier (cells := cells))
    (turn : Commit law accepted boundary) : Coordinate -> Balance :=
  law.delta incidence (accepted incidence)

abbrev SemanticHyperedge (commit : Commit law accepted boundary) :=
  Hyperedge
    Incidence
    (ULift.{max u v w x y z b h, max u v w x z}
      (Carrier (cells := cells)))
    (ULift.{max u v w x y z b h, max u v w x y z b h}
      (Commit law accepted boundary))
    (ULift.{max u v w x y z b h, 0} Digest)
    (ULift.{max u v w x y z b h, max y b} (Coordinate -> Balance))
    (fun state turn =>
      ⟨{ incidence := state.down.incidence
         state := turn.down.post state.down.incidence
         jointApex := declaration.header.apex }⟩)
    (fun _incidence state => ⟨state.down.jointApex⟩)
    (fun incidence _state _turn =>
      ⟨law.delta incidence (accepted incidence)⟩)

/-- The heterogeneous accepted family is one flat wide-pullback turn.  Each
incidence steps its own canonical cell; all observe the one joint apex. -/
def toHyperedge (commit : Commit law accepted boundary) :
    SemanticHyperedge commit where
  x := fun incidence =>
    ⟨{ incidence := incidence
       state := declaration.pre incidence
       jointApex := declaration.header.turnId }⟩
  t := ⟨commit⟩
  tid := ⟨declaration.header.apex⟩
  agree := by
    intro incidence
    rfl
  balanced := by
    apply (AddEquiv.ulift :
      ULift.{max u v w x y z b h, max y b} (Coordinate -> Balance) ≃+
        (Coordinate -> Balance)).injective
    rw [map_sum]
    funext coordinate
    simpa only [aggregateDelta, Finset.sum_apply, Pi.zero_apply] using
      congrFun commit.aggregateBalanced coordinate

@[simp] theorem hyperedge_pre_state (commit : Commit law accepted boundary)
    (incidence : Incidence) :
    (commit.toHyperedge.x incidence).down.state = declaration.pre incidence :=
  rfl

end Commit

/-! ## Total logical outcome and all-legs barrier -/

/-- Admission exposes either one fully validated joint commit or a rejection.
There is no constructor containing a partially accepted leg family. -/
inductive Admission
    (boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration)
    (Reject : Type h) : Type _
  | committed (accepted : declaration.AcceptedLegs)
      (commit : Commit law accepted boundary)
  | rejected (reason : Reject)

/-- Sequence the semantic all-legs barrier before joint validation.  The host
may accelerate either phase, but successful values must inhabit the exact Lean
types shown here. -/
def admit
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    {Reject : Type h}
    (validateLegs : Except Reject declaration.AcceptedLegs)
    (validateJoint : (accepted : declaration.AcceptedLegs) ->
      Except Reject (Commit law accepted boundary)) :
    Admission law boundary Reject :=
  match validateLegs with
  | .error reason => .rejected reason
  | .ok accepted =>
      match validateJoint accepted with
      | .error reason => .rejected reason
      | .ok commit => .committed accepted commit

/-- Rejection is logically atomic at every heterogeneous cell.  This says
nothing about a physical multi-database transaction; that remains a handler
obligation. -/
def Admission.logicalPost
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    {Reject : Type h} (outcome : Admission law boundary Reject)
    (incidence : Incidence) :
    CellState.Materialized (cells.materializer incidence) :=
  match outcome with
  | .committed accepted commit => commit.post incidence
  | .rejected _ => declaration.pre incidence

@[simp] theorem Admission.rejected_atomic
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    {Reject : Type h} (reason : Reject) (incidence : Incidence) :
    Admission.logicalPost (law := law)
      (Admission.rejected (law := law) (boundary := boundary) reason)
      incidence = declaration.pre incidence :=
  rfl

@[simp] theorem admit_leg_rejected
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    {Reject : Type h} (reason : Reject)
    (validateJoint : (accepted : declaration.AcceptedLegs) ->
      Except Reject (Commit law accepted boundary)) :
    admit law (.error reason) validateJoint = .rejected reason :=
  rfl

/-! ## Positive binary constructor and negative teeth -/

/-- The genuine two-cell positive: two accepted heterogeneous incidences with
distinct cell ids, one domain, a balanced resource law, and one joint evidence
value construct the same general N-cell commit (there is no transfer-specific
or call-forest structure). -/
def binaryCommit
    {cells : CellFamily.{u, v, w, x, 0} (Fin 2)}
    {declaration : Declaration.{u, v, w, x, y, 0} cells}
    {Coordinate : Type y} {Balance : Type b} [AddCommMonoid Balance]
    (law : ResourceLaw.{u, v, w, x, y, 0, b} declaration Coordinate Balance)
    (accepted : declaration.AcceptedLegs)
    (boundary : HandlerBoundary.{u, v, w, x, y, 0, h} declaration)
    (cellIdsDistinct : Function.Injective cells.cellId)
    (sharedDomain : forall incidence,
      (declaration.legs incidence).request.domain = declaration.header.domain)
    (aggregateBalanced : aggregateDelta law accepted = 0)
    (jointInput : JointCommitInput)
    (jointCommitExact : jointInput.jointCommit = declaration.header.apex)
    (jointEvidence : boundary.Evidence accepted jointInput) :
    Commit law accepted boundary where
  cellIdsDistinct := cellIdsDistinct
  sharedDomain := sharedDomain
  aggregateBalanced := aggregateBalanced
  jointInput := jointInput
  jointCommitExact := jointCommitExact
  jointEvidence := jointEvidence

/-- Cone data, exact accepted effects, and joint handler evidence cannot
manufacture conservation when any resource coordinate is nonzero. -/
theorem no_commit_of_nonzero_balance
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    (coordinate : Coordinate)
    (nonzero : forall accepted : declaration.AcceptedLegs,
      aggregateDelta law accepted coordinate ≠ 0) :
    IsEmpty (AdmittedCommit law boundary) :=
  ⟨fun admitted =>
    nonzero admitted.1
      (congrFun admitted.2.aggregateBalanced coordinate)⟩

/-- Distinct-cell policy has a load-bearing tooth: two different incidences
with the same cell id cannot be smuggled into a committed multi-cell turn. -/
theorem no_commit_of_conflicting_cell
    {boundary : HandlerBoundary.{u, v, w, x, y, z, h} declaration}
    (left right : Incidence) (different : left ≠ right)
    (sameCell : cells.cellId left = cells.cellId right) :
    IsEmpty (AdmittedCommit law boundary) :=
  ⟨fun admitted => different (admitted.2.cellIdsDistinct sameCell)⟩

/-- info: 'Minidregg.Kernel.MultiCellHyperedge.Declaration.post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Declaration.post_exact
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.PreparedTuple.accepted_posts_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTuple.accepted_posts_exact
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.PreparedTuple.accepted_mode_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTuple.accepted_mode_exact
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.PreparedTuple.declaration_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTuple.declaration_source_exact
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.PreparedTuple.declaration_joint_identity_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTuple.declaration_joint_identity_exact
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.Commit.toHyperedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Commit.toHyperedge
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.Admission.rejected_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Admission.rejected_atomic
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.binaryCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binaryCommit
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.no_commit_of_nonzero_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_nonzero_balance
/-- info: 'Minidregg.Kernel.MultiCellHyperedge.no_commit_of_conflicting_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_commit_of_conflicting_cell

end Minidregg.Kernel.MultiCellHyperedge
