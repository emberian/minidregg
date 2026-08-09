/-
# Theory.EffectDeclaration — typed effects derived from one declaration

This is the effect-side companion to `TypedAuthorization` and
`AuthorizationDeclaration`.  An author supplies one first-order `Declaration`:
a list of effects intrinsically indexed by one typed target.  Footprints,
full-width balance deltas, patches, wire data, the effect digest, guards, and
the executable checker are all derived from that declaration.

The checker accepts an existing request-indexed `Authorized` token.  It returns
a proof-relevant `AuthorizedEffect` only after request/effect binding, exact
per-resource balance, and guards succeed.  Rejection carries neither a post
state nor a patch.
-/
import Theory.AuthorizationDeclaration
import Theory.TypedAuthorization

namespace Minidregg.Theory.EffectDeclaration

open TypedAuthorization

/-! ## §1. Typed state keys, effects, and exact deltas -/

/-- Every mutable coordinate is kind-correct by construction. -/
inductive StateKey where
  | objectField (object : ResourceId .object) (field : Digest)
  | accountBalance (account : ResourceId .account) (resource : Digest)
  | programCode (program : ResourceId .program)
  deriving DecidableEq, Repr

/-- The semantic store is deliberately minimal: one exact integer per typed
state key. -/
abbrev Store := StateKey → Int

/-- A full-width balance delta.  `resource` is the complete `Digest` value;
there is no field-sized class, fold, or truncated namespace. -/
structure BalanceDelta where
  account : ResourceId .account
  resource : Digest
  amount : Int
  deriving DecidableEq, Repr

/-- Patch syntax contains data only. -/
inductive Mutation where
  | set (key : StateKey) (value : Int)
  | add (key : StateKey) (amount : Int)
  deriving DecidableEq, Repr

def Mutation.key : Mutation → StateKey
  | .set key _ => key
  | .add key _ => key

/-- Effects are indexed by the exact typed resource they authorize against.
No constructor carries a second, substitutable primary target. -/
inductive Effect : {kind : ResourceKind} → ResourceId kind → Type
  | objectWrite (target : ResourceId .object) (field : Digest)
      (expected replacement : Int) : Effect target
  | accountMove (source : ResourceId .account)
      (destination : ResourceId .account) (resource : Digest)
      (amount : Int) : Effect source
  | programInstall (target : ResourceId .program)
      (expected replacement : Int) : Effect target
  deriving DecidableEq, Repr

/-- The patch is a total projection of the typed effect. -/
def Effect.patch {kind : ResourceKind} {target : ResourceId kind} :
    Effect target → List Mutation
  | .objectWrite target field _ replacement =>
      [.set (.objectField target field) replacement]
  | .accountMove source destination resource amount =>
      [.add (.accountBalance source resource) (-amount),
       .add (.accountBalance destination resource) amount]
  | .programInstall target _ replacement =>
      [.set (.programCode target) replacement]

/-- The exact footprint is derived from patch keys, so the interpreter and
frame theorem cannot disagree about which coordinates may change. -/
def Effect.footprint {kind : ResourceKind} {target : ResourceId kind}
    (effect : Effect target) : List StateKey :=
  effect.patch.map Mutation.key

/-- Clear balance deltas are derived from the same constructor.  Object and
program effects carry no balance delta; a move carries matching debit/credit
under the exact same resource identifier. -/
def Effect.deltas {kind : ResourceKind} {target : ResourceId kind} :
    Effect target → List BalanceDelta
  | .objectWrite _ _ _ _ => []
  | .accountMove source destination resource amount =>
      [{ account := source, resource := resource, amount := -amount },
       { account := destination, resource := resource, amount := amount }]
  | .programInstall _ _ _ => []

/-- Guards are checked against the pre-state. -/
def Effect.guardCheck {kind : ResourceKind} {target : ResourceId kind}
    (effect : Effect target) (pre : Store) : Bool :=
  match effect with
  | .objectWrite target field expected _ =>
      decide (pre (.objectField target field) = expected)
  | .accountMove _ _ _ _ => true
  | .programInstall target expected _ =>
      decide (pre (.programCode target) = expected)

/-! ## §2. The single first-order declaration and its emitted projection -/

/-- The only authored effect object: a finite list of typed, first-order
constructors at one exact target.  It contains no function or proof field. -/
structure Declaration {kind : ResourceKind} (target : ResourceId kind) where
  effects : List (Effect target)

/-- Fully first-order, index-erased effect values. -/
inductive EffectWire where
  | objectWrite (target field : Nat) (expected replacement : Int)
  | accountMove (source destination resource : Nat) (amount : Int)
  | programInstall (target : Nat) (expected replacement : Int)
  deriving DecidableEq, Repr

def Effect.toWire {kind : ResourceKind} {target : ResourceId kind} :
    Effect target → EffectWire
  | .objectWrite target field expected replacement =>
      .objectWrite target.value field.value expected replacement
  | .accountMove source destination resource amount =>
      .accountMove source.value destination.value resource.value amount
  | .programInstall target expected replacement =>
      .programInstall target.value expected replacement

structure WireDeclaration where
  schemaVersion : Nat
  resourceKind : Nat
  target : Nat
  effects : List EffectWire
  deriving DecidableEq, Repr

def Declaration.toWire {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : WireDeclaration where
  schemaVersion := 1
  resourceKind := AuthorizationDeclaration.resourceKindTag kind
  target := target.value
  effects := declaration.effects.map Effect.toWire

def encodeInt : Int → Nat
  | .ofNat value => 2 * value
  | .negSucc value => 2 * value + 1

def EffectWire.words : EffectWire → List Nat
  | .objectWrite target field expected replacement =>
      [1, target, field, encodeInt expected, encodeInt replacement]
  | .accountMove source destination resource amount =>
      [2, source, destination, resource, encodeInt amount]
  | .programInstall target expected replacement =>
      [3, target, encodeInt expected, encodeInt replacement]

def WireDeclaration.words (wire : WireDeclaration) : List Nat :=
  [wire.schemaVersion, wire.resourceKind, wire.target, wire.effects.length] ++
    wire.effects.flatMap EffectWire.words

/-- A deterministic declaration digest used by the existing request field.
The exact wire word is the authoritative first-order artifact. -/
def digestWords : List Nat → Nat :=
  List.foldl (fun accumulator word => accumulator * 16777619 + word + 1)
    2166136261

def Declaration.digest {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Digest :=
  ⟨digestWords declaration.toWire.words⟩

def Declaration.patch {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List Mutation :=
  declaration.effects.flatMap Effect.patch

def Declaration.footprint {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List StateKey :=
  (declaration.patch.map Mutation.key).eraseDups

def Declaration.deltas {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List BalanceDelta :=
  declaration.effects.flatMap Effect.deltas

def Declaration.resources {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List Digest :=
  (declaration.deltas.map BalanceDelta.resource).eraseDups

def deltaSum (deltas : List BalanceDelta) (resource : Digest) : Int :=
  (deltas.map fun delta =>
    if delta.resource = resource then delta.amount else 0).sum

/-- Exact conservation is stated independently for every COMPLETE resource id
which occurs in the declaration. -/
def Declaration.ExactBalance {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Prop :=
  ∀ resource ∈ declaration.resources,
    deltaSum declaration.deltas resource = 0

def Declaration.balanceCheck {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Bool :=
  declaration.resources.all fun resource =>
    decide (deltaSum declaration.deltas resource = 0)

@[simp] theorem Declaration.balanceCheck_eq_true_iff
    {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) :
    declaration.balanceCheck = true ↔ declaration.ExactBalance := by
  simp [Declaration.balanceCheck, Declaration.ExactBalance]

/-! ## §3. Derived patch, frame, and exact balance laws -/

def applyMutation (mutation : Mutation) (state : Store) : Store :=
  match mutation with
  | .set key value => Function.update state key value
  | .add key amount => Function.update state key (state key + amount)

def applyPatch : List Mutation → Store → Store
  | [], state => state
  | mutation :: rest, state => applyPatch rest (applyMutation mutation state)

theorem applyMutation_frame (mutation : Mutation) (state : Store)
    (key : StateKey) (outside : key ≠ mutation.key) :
    applyMutation mutation state key = state key := by
  cases mutation with
  | set changed value =>
      change key ≠ changed at outside
      simp [applyMutation, outside]
  | add changed amount =>
      change key ≠ changed at outside
      simp [applyMutation, outside]

theorem applyPatch_frame (patch : List Mutation) (state : Store)
    (key : StateKey) (outside : key ∉ patch.map Mutation.key) :
    applyPatch patch state key = state key := by
  induction patch generalizing state with
  | nil => rfl
  | cons mutation rest induction =>
      have split : key ≠ mutation.key ∧ key ∉ rest.map Mutation.key := by
        simpa using outside
      calc
        applyPatch (mutation :: rest) state key =
            applyPatch rest (applyMutation mutation state) key := rfl
        _ = applyMutation mutation state key :=
          induction (state := applyMutation mutation state) split.2
        _ = state key := applyMutation_frame mutation state key split.1

theorem deltaSum_append (left right : List BalanceDelta)
    (resource : Digest) :
    deltaSum (left ++ right) resource =
      deltaSum left resource + deltaSum right resource := by
  simp [deltaSum, List.map_append, List.sum_append]

theorem Effect.deltaSum_zero {kind : ResourceKind}
    {target : ResourceId kind} (effect : Effect target) (resource : Digest) :
    deltaSum effect.deltas resource = 0 := by
  cases effect with
  | objectWrite => simp [Effect.deltas, deltaSum]
  | accountMove source destination moved amount =>
      by_cases same : moved = resource
      · simp [Effect.deltas, deltaSum, same]
      · simp [Effect.deltas, deltaSum, same]
  | programInstall => simp [Effect.deltas, deltaSum]

theorem effects_deltaSum_zero {kind : ResourceKind}
    {target : ResourceId kind} (effects : List (Effect target))
    (resource : Digest) :
    deltaSum (effects.flatMap Effect.deltas) resource = 0 := by
  induction effects with
  | nil => simp [deltaSum]
  | cons effect rest induction =>
      simp [deltaSum_append, Effect.deltaSum_zero, induction]

/-- Every declared constructor conserves every exact resource namespace. -/
theorem Declaration.exactBalance {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target) :
    declaration.ExactBalance := by
  intro resource _
  exact effects_deltaSum_zero declaration.effects resource

def Declaration.guardsCheck {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (pre : Store) : Bool :=
  declaration.effects.all fun effect => effect.guardCheck pre

def Declaration.evaluate {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (pre : Store) : Option Store :=
  if declaration.guardsCheck pre = true
  then some (applyPatch declaration.patch pre)
  else none

/-- The derived interpreter changes nothing outside the exact derived
footprint. -/
theorem Declaration.evaluate_frame {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (pre post : Store) (evaluated : declaration.evaluate pre = some post)
    (key : StateKey) (outside : key ∉ declaration.footprint) :
    post key = pre key := by
  have outsidePatch : key ∉ declaration.patch.map Mutation.key := by
    simpa [Declaration.footprint] using outside
  by_cases guards : declaration.guardsCheck pre = true
  · simp [Declaration.evaluate, guards] at evaluated
    subst post
    exact applyPatch_frame declaration.patch pre key outsidePatch
  · simp [Declaration.evaluate, guards] at evaluated

/-! ## §4. Derived request binding and proof-relevant admission -/

def Declaration.requestBindingCheck {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (request : Request kind) : Bool :=
  decide (request.effectsDigest = declaration.digest)

@[simp] theorem Declaration.requestBindingCheck_eq_true_iff
    {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (request : Request kind) :
    declaration.requestBindingCheck request = true ↔
      request.effectsDigest = declaration.digest := by
  simp [Declaration.requestBindingCheck]

/-- The proof-relevant token created only after all executable effect checks. -/
structure AuthorizedEffect {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (declaration : Declaration request.target) (pre post : Store) : Type where
  authorization : Authorized portal authState request
  requestBound : request.effectsDigest = declaration.digest
  exactBalance : declaration.ExactBalance
  evaluated : declaration.evaluate pre = some post

inductive RejectReason where
  | requestBinding
  | balance
  | guard
  deriving DecidableEq, Repr

inductive CheckOutcome {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (declaration : Declaration request.target) (pre : Store) : Type where
  | accepted (post : Store)
      (token : AuthorizedEffect (portal := portal) (authState := authState)
        declaration pre post)
  | rejected (reason : RejectReason)

/-- Executable effect admission.  The state patch exists only in `accepted`. -/
def check {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (authorization : Authorized portal authState request)
    (declaration : Declaration request.target) (pre : Store) :
    CheckOutcome (portal := portal) (authState := authState) declaration pre :=
  if requestBound : declaration.requestBindingCheck request = true then
    if balanced : declaration.balanceCheck = true then
      match evaluated : declaration.evaluate pre with
      | none => .rejected .guard
      | some post => .accepted post
          { authorization := authorization
            requestBound :=
              (declaration.requestBindingCheck_eq_true_iff request).mp requestBound
            exactBalance :=
              (Declaration.balanceCheck_eq_true_iff declaration).mp balanced
            evaluated := evaluated }
    else .rejected .balance
  else .rejected .requestBinding

def CheckOutcome.patch? {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {declaration : Declaration request.target} {pre : Store} :
    CheckOutcome (portal := portal) (authState := authState) declaration pre →
      Option Store
  | .accepted post _ => some post
  | .rejected _ => none

/-- Reject-before-patch: every refusal has no replacement state. -/
theorem check_rejected_no_patch {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (authorization : Authorized portal authState request)
    (declaration : Declaration request.target) (pre : Store)
    (reason : RejectReason)
    (rejected : check authorization declaration pre = .rejected reason) :
    (check authorization declaration pre).patch? = none := by
  rw [rejected]
  rfl

/-- Every accepted token inherits the exact frame law. -/
theorem AuthorizedEffect.frame {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {declaration : Declaration request.target} {pre post : Store}
    (token : AuthorizedEffect (portal := portal) (authState := authState)
      declaration pre post)
    (key : StateKey) (outside : key ∉ declaration.footprint) :
    post key = pre key :=
  declaration.evaluate_frame pre post token.evaluated key outside

/-- Every accepted token exposes exact, full-resource balance. -/
theorem AuthorizedEffect.balance {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {declaration : Declaration request.target} {pre post : Store}
    (token : AuthorizedEffect (portal := portal) (authState := authState)
      declaration pre post) :
    ∀ resource ∈ declaration.resources,
      deltaSum declaration.deltas resource = 0 :=
  token.exactBalance

/-- The declaration's target is definitionally the authorized request target.
An unequal replacement target cannot be claimed by the token. -/
def Declaration.boundTarget {kind : ResourceKind} {target : ResourceId kind}
    (_declaration : Declaration target) : ResourceId kind := target

@[simp] theorem Declaration.boundTarget_eq {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target) :
    declaration.boundTarget = target := rfl

theorem AuthorizedEffect.no_target_substitution
    {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {declaration : Declaration request.target} {pre post : Store}
    (_token : AuthorizedEffect (portal := portal) (authState := authState)
      declaration pre post)
    (replacement : ResourceId kind) (different : replacement ≠ request.target) :
    declaration.boundTarget ≠ replacement := by
  simpa using different.symm

end Minidregg.Theory.EffectDeclaration
