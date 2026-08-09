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
import Theory.CellState
import Theory.EffectDeclaration

namespace Minidregg.Theory.DeclaredTurn

open TypedAuthorization
open AuthorizationDeclaration
open EffectDeclaration
open CellState

/-! ## §1. The canonical cell carrier for declared effects -/

/-- Effects use the typed state key as their cell field schema.  There is no
second extension map.  This declaration has no separate resource-package lane,
because exact resource balances already inhabit typed `accountBalance` keys. -/
def effectSchema : CellState.Schema where
  Field := EffectDeclaration.StateKey
  FieldType := fun _ => Int
  Resource := Empty
  ResourceType := fun resource => nomatch resource
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

def logicalOfStore (store : EffectDeclaration.Store) :
    CellState.LogicalState effectSchema where
  fields := store
  resources := fun resource => nomatch resource

def storeOfLogical (logical : CellState.LogicalState effectSchema) :
    EffectDeclaration.Store :=
  logical.fields

@[simp] theorem storeOfLogical_logicalOfStore (store : EffectDeclaration.Store) :
    storeOfLogical (logicalOfStore store) = store :=
  rfl

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
  cost := seed.cost

/-! ## §3. The one declared turn and total execution -/

/-- One complete transaction declaration.  The presentation is indexed by the
request derived from the other fields, so it cannot name an alternate request. -/
structure Declaration (portal : Portal)
    (materializer : CellState.Materializer effectSchema Digest)
    (kind : ResourceKind) where
  seed : RequestSeed kind
  effects : EffectDeclaration.Declaration seed.target
  pre : CellState.Materialized materializer
  presentation : AuthorizationDeclaration.Presentation portal
    (seed.derive effects.digest pre.root)

def Declaration.request {portal : Portal}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    Request kind :=
  declaration.seed.derive declaration.effects.digest declaration.pre.root

@[simp] theorem Declaration.request_target {portal : Portal}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    declaration.request.target = declaration.seed.target :=
  rfl

@[simp] theorem Declaration.request_effectsDigest {portal : Portal}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    declaration.request.effectsDigest = declaration.effects.digest :=
  rfl

@[simp] theorem Declaration.request_preStateRoot {portal : Portal}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    declaration.request.preStateRoot = declaration.pre.root :=
  rfl

def Declaration.preStore {portal : Portal}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} (declaration : Declaration portal materializer kind) :
    EffectDeclaration.Store :=
  storeOfLogical declaration.pre.logical

structure Commit {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind)
    (postStore : EffectDeclaration.Store) : Type where
  effect : EffectDeclaration.AuthorizedEffect
    (portal := portal) (authState := state) (request := declaration.request)
    declaration.effects declaration.preStore postStore

def Commit.post {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (_commit : Commit (state := state) declaration postStore) :
    CellState.Materialized materializer :=
  CellState.materialize materializer (logicalOfStore postStore)

def Commit.preRoot {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (_commit : Commit (state := state) declaration postStore) : Digest :=
  declaration.pre.root

def Commit.postRoot {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore) : Digest :=
  commit.post.root

inductive RejectReason where
  | authorization (failedCheck : AuthorizationDeclaration.Check)
  | effect (reason : EffectDeclaration.RejectReason)
  deriving DecidableEq, Repr

inductive Outcome {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind) : Type where
  | committed (postStore : EffectDeclaration.Store)
  | rejected (reason : RejectReason)

/-- Pure data execution.  Authorization runs first.  Only its accepted branch
checks declaration binding, exact balance, and guards before evaluating the
derived patch.  No proof object is selected on this executable path. -/
def execute {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind) :
    Outcome state declaration :=
  match AuthorizationDeclaration.verify (state := state)
      declaration.presentation with
  | .rejected failedCheck => .rejected (.authorization failedCheck)
  | .accepted =>
      if declaration.effects.requestBindingCheck declaration.request = true then
        if declaration.effects.balanceCheck = true then
          match declaration.effects.evaluate declaration.preStore with
          | none => .rejected (.effect .guard)
          | some postStore => .committed postStore
        else .rejected (.effect .balance)
      else .rejected (.effect .requestBinding)

/-- Data acceptance has a semantic proof object.  The only authorization
bridge is the existing admission theorem; `Nonempty` elimination remains
inside `Prop`, and execution itself never selects an authorization witness. -/
theorem execute_committed_sound {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind}
    (declaration : Declaration portal materializer kind)
    (postStore : EffectDeclaration.Store)
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
              declaration.effects.evaluate declaration.preStore with
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
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind} :
    Outcome state declaration → CellState.Materialized materializer
  | .committed postStore =>
      CellState.materialize materializer (logicalOfStore postStore)
  | .rejected _ => declaration.pre

@[simp] theorem Outcome.rejected_materialized {portal : Portal}
    {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    (reason : RejectReason) :
    (Outcome.rejected (state := state) (declaration := declaration) reason).materialized =
      declaration.pre :=
  rfl

/-- Any rejected execution leaves the exact canonical materialization unchanged. -/
theorem execute_rejected_unchanged {portal : Portal} (state : AuthState)
    {materializer : CellState.Materializer effectSchema Digest}
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
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (_commit : Commit (state := state) declaration postStore) :
    declaration.effects.boundTarget = declaration.request.target :=
  rfl

/-- The only footprint attached to commit is the declaration-derived one. -/
def Commit.footprint {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (_commit : Commit (state := state) declaration postStore) :
    List EffectDeclaration.StateKey :=
  declaration.effects.footprint

@[simp] theorem Commit.footprint_exact {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore) :
    commit.footprint = declaration.effects.footprint :=
  rfl

/-- Commit changes no cell field outside the exact derived footprint. -/
theorem Commit.frame {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore)
    (key : EffectDeclaration.StateKey)
    (outside : key ∉ commit.footprint) :
    commit.post.logical.fields key = declaration.pre.logical.fields key := by
  change postStore key = declaration.preStore key
  exact commit.effect.frame key (by simpa [Commit.footprint] using outside)

/-- Commit conserves every complete resource id named by its exact deltas. -/
theorem Commit.balance {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore) :
    ∀ resource ∈ declaration.effects.resources,
      EffectDeclaration.deltaSum declaration.effects.deltas resource = 0 :=
  commit.effect.balance

/-- The pre-root is the root of the sole supplied canonical pre-state and is
also definitionally the root in the derived request. -/
theorem Commit.preRoot_derived {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore) :
    commit.preRoot = declaration.request.preStateRoot :=
  rfl

/-- The post-root is recomputed from the committed post store's canonical
encoding; no independent post-root input exists. -/
theorem Commit.postRoot_derived {portal : Portal} {state : AuthState}
    {materializer : CellState.Materializer effectSchema Digest}
    {kind : ResourceKind} {declaration : Declaration portal materializer kind}
    {postStore : EffectDeclaration.Store}
    (commit : Commit (state := state) declaration postStore) :
    commit.postRoot =
      materializer.rootBytes (materializer.codec.encode
        (logicalOfStore postStore)) :=
  rfl

end Minidregg.Theory.DeclaredTurn
