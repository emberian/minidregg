/-
# Theory.DeclaredTurn — one executable declared transaction

A declared turn owns one request seed, one target-indexed effect declaration,
one canonical pre-state, and raw authorization presentation data.  The complete
request is derived from those values: its effect digest comes from the effect
declaration and its pre-state root comes from the canonical materialization.

Execution runs the existing authorization decision tree first, then the
existing effect checker.  Only their joint acceptance constructs `Commit`.
Rejection materializes to the exact original state; accepted post-state and
both roots are projections, never caller-supplied witnesses.
-/
import Theory.AuthorizationDeclaration
import Theory.CanonicalTransition
import Theory.EffectDeclaration

namespace Minidregg.Theory.DeclaredTurn

open TypedAuthorization
open AuthorizationDeclaration
open EffectDeclaration
open CellState
open Minidregg.Theory.Store

/-! ## §1. The canonical cell carrier for declared effects

The cell layout is `EffectDeclaration.effectLayout`: the effect evaluator and
the canonical cell read and write the same sparse store, so there is no
reification between a semantic store and the cell. -/

/-! ## §2. Request derivation -/

/-- All request inputs except the two values owned by the declaration itself:
`effectsDigest` and `preStateRoot`. -/
structure RequestSeed (kind : ResourceKind) where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  target : ResourceId kind
  verb : Verb kind
  argsDigest : Digest
  nonce : Nat
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch
  policyRevision : PolicyRevision
  cost : Nat

def RequestSeed.derive {kind : ResourceKind} (seed : RequestSeed kind)
    (effectsDigest preStateRoot : Digest) : Request kind where
  domain := seed.domain
  semantics := seed.semantics
  federation := seed.federation
  subject := seed.subject
  subjectKeyEpoch := seed.subjectKeyEpoch
  target := seed.target
  verb := seed.verb
  argsDigest := seed.argsDigest
  effectsDigest := effectsDigest
  nonce := seed.nonce
  height := seed.height
  preStateRoot := preStateRoot
  policyId := seed.policyId
  policyEpoch := seed.policyEpoch
  policyRevision := seed.policyRevision
  cost := seed.cost

/-! ## §3. The one declared turn and total execution -/

/-- One complete transaction declaration.  The presentation is indexed by the
request derived from the other fields, so it cannot name an alternate request. -/
structure Declaration (portal : Portal)
    (materializer : CellState.Materializer effectLayout Digest)
    (kind : ResourceKind) where
  seed : RequestSeed kind
  effects : EffectDeclaration.Declaration seed.target
  pre : CellState.Materialized materializer
  presentation : AuthorizationDeclaration.Presentation portal
    (seed.derive effects.digest pre.root)

def Declaration.request {portal : Portal}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    Request kind :=
  declaration.seed.derive declaration.effects.digest declaration.pre.root

@[simp] theorem Declaration.request_target {portal : Portal}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    declaration.request.target = declaration.seed.target :=
  rfl

@[simp] theorem Declaration.request_effectsDigest {portal : Portal}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    declaration.request.effectsDigest = declaration.effects.digest :=
  rfl

@[simp] theorem Declaration.request_preStateRoot {portal : Portal}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    declaration.request.preStateRoot = declaration.pre.root :=
  rfl

structure Commit {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind)
    (postStore : Store effectLayout) : Type where
  effect : EffectDeclaration.AuthorizedEffect
    (portal := portal) (authState := state) (request := declaration.request)
    declaration.effects declaration.pre.logical postStore

def Commit.post {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (_commit : Commit (state := state) declaration postStore) :
    CellState.Materialized materializer :=
  CellState.materialize materializer postStore

def Commit.preRoot {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (_commit : Commit (state := state) declaration postStore) : Digest :=
  declaration.pre.root

def Commit.postRoot {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) : Digest :=
  commit.post.root

inductive RejectReason where
  | authorization (failedCheck : AuthorizationDeclaration.Check)
  | effect (reason : EffectDeclaration.RejectReason)
  deriving DecidableEq, Repr

inductive Outcome {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind) : Type where
  | committed (postStore : Store effectLayout)
  | rejected (reason : RejectReason)

/-- Pure data execution.  Authorization runs first.  Only its accepted branch
checks declaration binding, exact balance, and guards before evaluating the
derived patch.  No proof object is selected on this executable path. -/
def execute {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind) :
    Outcome state declaration :=
  match AuthorizationDeclaration.verify (state := state)
      declaration.presentation with
  | .rejected failedCheck => .rejected (.authorization failedCheck)
  | .accepted =>
      if declaration.effects.requestBindingCheck declaration.request = true then
        if declaration.effects.balanceCheck = true then
          match declaration.effects.evaluate declaration.pre.logical with
          | none => .rejected (.effect .guard)
          | some postStore => .committed postStore
        else .rejected (.effect .balance)
      else .rejected (.effect .requestBinding)

/-- Data acceptance has a semantic proof object.  The only authorization
bridge is the existing admission theorem; `Nonempty` elimination remains
inside `Prop`, and execution itself never selects an authorization witness. -/
theorem execute_committed_sound {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind)
    (postStore : Store effectLayout)
    (committed : execute state declaration = .committed postStore) :
    Nonempty (Commit (state := state) declaration postStore) := by
  unfold execute at committed
  generalize decisionEq :
      AuthorizationDeclaration.verify (state := state)
        declaration.presentation = decision at committed
  cases decision with
  | rejected failedCheck =>
      simp at committed
  | accepted =>
      have authorized :=
        AuthorizationDeclaration.verify_accepted_authorized
          declaration.presentation decisionEq
      rcases authorized with ⟨authorization⟩
      by_cases requestBound :
          declaration.effects.requestBindingCheck declaration.request = true
      · by_cases balanced : declaration.effects.balanceCheck = true
        · cases evaluated :
              declaration.effects.evaluate declaration.pre.logical with
          | none =>
              simp [requestBound, balanced, evaluated] at committed
          | some candidate =>
              have candidate_eq : candidate = postStore := by
                simpa [requestBound, balanced, evaluated] using committed
              subst postStore
              refine ⟨{ effect := ?_ }⟩
              exact
                { authorization := authorization
                  requestBound :=
                    (declaration.effects.requestBindingCheck_eq_true_iff
                      declaration.request).mp requestBound
                  exactBalance :=
                    (EffectDeclaration.Declaration.balanceCheck_eq_true_iff
                      declaration.effects).mp balanced
                  evaluated := evaluated }
        · simp [requestBound, balanced] at committed
      · simp [requestBound] at committed

/-- Materialized state after execution.  Refusal is definitionally atomic. -/
def Outcome.materialized {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind} :
    Outcome state declaration → CellState.Materialized materializer
  | .committed postStore =>
      CellState.materialize materializer postStore
  | .rejected _ => declaration.pre

@[simp] theorem Outcome.rejected_materialized {portal : Portal}
    {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    (reason : RejectReason) :
    (Outcome.rejected (state := state) (declaration := declaration) reason).materialized =
      declaration.pre :=
  rfl

/-- Any rejected execution leaves the exact canonical materialization unchanged. -/
theorem execute_rejected_unchanged {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind)
    (reason : RejectReason)
    (rejected : execute state declaration = .rejected reason) :
    (execute state declaration).materialized = declaration.pre := by
  rw [rejected]
  rfl

/-! ## §5. Commit laws -/

/-- The committed effect target is exactly the derived request target. -/
theorem Commit.target_exact {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (_commit : Commit (state := state) declaration postStore) :
    declaration.effects.boundTarget = declaration.request.target :=
  rfl

/-- The only footprint attached to commit is the declaration-derived one. -/
def Commit.footprint {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (_commit : Commit (state := state) declaration postStore) :
    List EffectDeclaration.StateKey :=
  declaration.effects.footprint

@[simp] theorem Commit.footprint_exact {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    commit.footprint = declaration.effects.footprint :=
  rfl

/-- Commit changes no cell address outside the exact derived footprint. -/
theorem Commit.frame {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore)
    (key : StateKey)
    (outside : key ∉ commit.footprint) :
    commit.post.logical key.address = declaration.pre.logical key.address :=
  commit.effect.frame key outside

/-- Commit conserves every complete resource id named by its exact deltas. -/
theorem Commit.balance {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    ∀ resource ∈ declaration.effects.resources,
      EffectDeclaration.deltaSum declaration.effects.deltas resource = 0 :=
  commit.effect.balance

/-- The pre-root is the root of the sole supplied canonical pre-state and is
also definitionally the root in the derived request. -/
theorem Commit.preRoot_derived {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    commit.preRoot = declaration.request.preStateRoot :=
  rfl

/-- The post-root is the materializer's root of the committed post store; no
independent post-root input exists. -/
theorem Commit.postRoot_derived {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    commit.postRoot = materializer.rootOf postStore :=
  rfl

/-! ## §6. The commit as a validated patch, and its canonical transition

The evaluator runs the lowered guarded patch (`EffectDeclaration.lowerPatch`).
That patch, quoted against the request's pre-root, is a `ValidatedPatch` of the
pre-cell, and its application is the commit's post.  The canonical transition
of a declared commit is therefore `PreparedTurn.ofValidatedPatch` of it: its
footprint is the lowered patch's syntactic write footprint and its frame is
`Store.Patch.run_frame`. -/

/-- The guarded patch a commit runs, read at the declaration's pre-store. -/
def Commit.patch {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (_commit : Commit (state := state) declaration postStore) :
    Patch effectLayout :=
  lowerPatch declaration.effects.patch declaration.pre.logical

/-- The commit executes its lowered patch exactly from the pre-store. -/
theorem Commit.executes {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    Patch.Executes declaration.pre.logical commit.patch postStore :=
  declaration.effects.evaluate_executes _ _ commit.effect.evaluated

/-- The lowered patch, quoted against the derived request's pre-root, is
validated against the pre-cell. -/
theorem Commit.validated {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    ValidatedPatch materializer declaration.pre declaration.request.preStateRoot
      commit.patch := by
  obtain ⟨validated, _⟩ := validate_accepts materializer declaration.pre
    declaration.request.preStateRoot commit.patch rfl commit.executes.1
  exact validated

/-- The validated application is the commit's post. -/
theorem Commit.validated_apply {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    commit.validated.apply = commit.post :=
  Materialized.ext commit.executes.2

/-- The commit's derived write footprint is exactly its declared footprint, as
addresses. -/
theorem Commit.patch_writeFootprint {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : Store effectLayout}
    (commit : Commit (state := state) declaration postStore) :
    Patch.writeFootprint commit.patch =
      (declaration.effects.patch.map fun mutation => mutation.key.address).toFinset :=
  lowerPatch_writeFootprint _ _

end Minidregg.Theory.DeclaredTurn

namespace Minidregg.Theory.CanonicalTransition

open TypedAuthorization
open EffectDeclaration
open Minidregg.Theory.Store

/-- An ordinary declared commit is the canonical transition of its validated
lowered patch.  Ordinary turns carry no guarded-resume nullifier. -/
def PreparedTurn.ofDeclaredCommit
    {portal : Portal} {authState : AuthState}
    {M : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : Store effectLayout}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    PreparedTurn M declaration.pre Empty :=
  PreparedTurn.ofValidatedPatch commit.validated none

/-- The adapter's post is the commit's post. -/
theorem PreparedTurn.ofDeclaredCommit_post
    {portal : Portal} {authState : AuthState}
    {M : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : Store effectLayout}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).post = commit.post :=
  commit.validated_apply

/-- The adapter's footprint is the commit's declared footprint, as addresses. -/
theorem PreparedTurn.ofDeclaredCommit_footprint
    {portal : Portal} {authState : AuthState}
    {M : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : Store effectLayout}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).delta.footprint =
      (declaration.effects.patch.map fun mutation => mutation.key.address).toFinset :=
  commit.patch_writeFootprint

@[simp] theorem PreparedTurn.ofDeclaredCommit_nullifier
    {portal : Portal} {authState : AuthState}
    {M : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : Store effectLayout}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).nullifier = (none : Option Empty) :=
  rfl

/-- The adapter preserves the request's canonical pre-root. -/
theorem PreparedTurn.ofDeclaredCommit_preRoot
    {portal : Portal} {authState : AuthState}
    {M : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : Store effectLayout}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).preRoot =
      declaration.request.preStateRoot :=
  PreparedTurn.ofValidatedPatch_preRoot commit.validated none

/-- The adapter's post-root is the commit's canonical post-root. -/
theorem PreparedTurn.ofDeclaredCommit_postRoot
    {portal : Portal} {authState : AuthState}
    {M : CellState.Materializer effectLayout Digest}
    {kind : ResourceKind}
    {declaration : DeclaredTurn.Declaration portal M kind}
    {postStore : Store effectLayout}
    (commit : DeclaredTurn.Commit (state := authState) declaration postStore) :
    (PreparedTurn.ofDeclaredCommit commit).postRoot = commit.postRoot := by
  change (PreparedTurn.ofDeclaredCommit commit).post.root = commit.post.root
  rw [PreparedTurn.ofDeclaredCommit_post]

/-- info: 'Minidregg.Theory.DeclaredTurn.Commit.validated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DeclaredTurn.Commit.validated
/-- info: 'Minidregg.Theory.CanonicalTransition.PreparedTurn.ofDeclaredCommit_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PreparedTurn.ofDeclaredCommit_post

end Minidregg.Theory.CanonicalTransition
