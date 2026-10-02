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

State is the one sparse store (`Theory.Store`) over `effectLayout`: a single
RAM namespace keyed by `StateKey` with `Int` values.  Mutations are data; the
executor lowers them, in order, to guarded `Store.Op`s whose `before` values are
read at the store their prefix produced, and runs that patch.  There is no
second, total store: a guard or a balance reads an absent key as `0` through
`read`, and absence stays a value of the representation.
-/
import Theory.AuthorizationDeclaration
import Theory.Store
import Theory.TypedAuthorization

namespace Minidregg.Theory.EffectDeclaration

open TypedAuthorization
open Minidregg.Theory.Store

/-! ## §1. Typed state keys, effects, and exact deltas -/

/-- Every mutable coordinate is kind-correct by construction.

`fieldDeclared` and `fieldsOpen` are a declared cell's **declaration**
(K-FIELD-CLOSURE, `Kernel.FieldClosure`): the fields the cell may hold,
written at birth.  No action writes them (`DeclaredActionLowering.writableKeyCheck`),
so a cell's declaration is fixed for its life. -/
inductive StateKey where
  | objectField (object : ResourceId .object) (field : Digest)
  | accountBalance (account : ResourceId .account) (resource : Digest)
  | programCode (program : ResourceId .program)
  /-- The cell's hiding key (K-NARROW-HIDE): the blinding that keys every
  entry's salt under the store root.  Set at birth by the owner's client; no
  action writes it (`writableKeyCheck` refuses it) and no reader receives it. -/
  | blinding
  /-- The cell declares that it may hold object field `field`. -/
  | fieldDeclared (object : ResourceId .object) (field : Digest)
  /-- The cell declares that it may hold any object field: an open kind. -/
  | fieldsOpen (object : ResourceId .object)
  deriving DecidableEq, Repr

/-- The declared-effect layout: one RAM namespace whose keys are the typed
state keys and whose values are exact integers. -/
abbrev effectLayout : Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => StateKey
  Value := fun _ => Int
  discipline := fun _ => .ram

/-- The store address of one typed state key. -/
def StateKey.address (key : StateKey) : Address effectLayout := ⟨(), key⟩

theorem StateKey.address_injective : Function.Injective StateKey.address := by
  intro left right same
  simpa [StateKey.address] using same

/-- The integer reading of a key: absence reads as `0`.  This is a view for
guards and balances, not a second store. -/
def read (store : Store effectLayout) (key : StateKey) : Int :=
  (store key.address).getD 0

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
    (effect : Effect target) (pre : Store effectLayout) : Bool :=
  match effect with
  | .objectWrite target field expected _ =>
      decide (read pre (.objectField target field) = expected)
  | .accountMove _ _ _ _ => true
  | .programInstall target expected _ =>
      decide (read pre (.programCode target) = expected)

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

/-- The one integer-to-natural encoding (zigzag): nonnegatives to evens,
negatives to odds.  Declaration words, action codes and every store-coded
integer value (`Compiler.IntStream`) use this map and its inverse. -/
def encodeInt : Int → Nat
  | .ofNat value => 2 * value
  | .negSucc value => 2 * value + 1

def decodeInt : Nat -> Int
  | n => if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

@[simp] theorem decodeInt_encodeInt (value : Int) :
    decodeInt (encodeInt value) = value := by
  cases value with
  | ofNat value => simp [decodeInt, encodeInt]
  | negSucc value => simp [decodeInt, encodeInt]; omega

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

/-- The value a mutation writes, read at the store it runs against. -/
def Mutation.value (mutation : Mutation) (store : Store effectLayout) : Int :=
  match mutation with
  | .set _ value => value
  | .add key amount => read store key + amount

/-- Lower one mutation to the guarded operation it performs at `store`: an
overwrite guarded by the exact present value, or an allocation at an absent
key.  The guard is read from `store`, so it holds there by construction. -/
def Mutation.op (mutation : Mutation) (store : Store effectLayout) :
    Op effectLayout :=
  match store mutation.key.address with
  | some before => .write () mutation.key before (mutation.value store)
  | none => .allocate () mutation.key (mutation.value store)

/-- Lower a mutation list in order: each operation's guard is read at the
store its prefix produced. -/
def lowerPatch : List Mutation → Store effectLayout → Patch effectLayout
  | [], _ => []
  | mutation :: rest, store =>
      mutation.op store :: lowerPatch rest ((mutation.op store).apply store)

/-- The executor: run the lowered guarded patch. -/
def applyPatch (mutations : List Mutation) (store : Store effectLayout) :
    Store effectLayout :=
  Patch.run store (lowerPatch mutations store)

theorem Mutation.op_enabled (mutation : Mutation) (store : Store effectLayout) :
    (mutation.op store).Enabled store := by
  unfold Mutation.op
  split
  · rename_i before present
    exact ⟨rfl, present⟩
  · rename_i absent
    exact ⟨by decide, absent⟩

theorem Mutation.op_writeAddress (mutation : Mutation) (store : Store effectLayout) :
    (mutation.op store).writeAddress? = some mutation.key.address := by
  unfold Mutation.op
  split <;> rfl

theorem Mutation.op_apply (mutation : Mutation) (store : Store effectLayout) :
    (mutation.op store).apply store =
      store.set mutation.key.address (some (mutation.value store)) := by
  unfold Mutation.op
  split <;> rfl

/-- The lowering is valid at the store it was read from. -/
theorem lowerPatch_valid (mutations : List Mutation) (store : Store effectLayout) :
    Patch.ValidFrom store (lowerPatch mutations store) := by
  induction mutations generalizing store with
  | nil => trivial
  | cons mutation rest ih =>
      exact ⟨mutation.op_enabled store, ih _⟩

/-- The lowered patch writes exactly the mutated keys, in order. -/
theorem lowerPatch_writeAddresses (mutations : List Mutation)
    (store : Store effectLayout) :
    (lowerPatch mutations store).filterMap Op.writeAddress? =
      mutations.map fun mutation => mutation.key.address := by
  induction mutations generalizing store with
  | nil => rfl
  | cons mutation rest ih =>
      simp [lowerPatch, Mutation.op_writeAddress, ih]

theorem lowerPatch_writeFootprint (mutations : List Mutation)
    (store : Store effectLayout) :
    Patch.writeFootprint (lowerPatch mutations store) =
      (mutations.map fun mutation => mutation.key.address).toFinset := by
  rw [Patch.writeFootprint, lowerPatch_writeAddresses]

/-- The executor changes no key outside the mutated keys.  This is
`Store.Patch.run_frame` on the lowered patch. -/
theorem applyPatch_frame (mutations : List Mutation) (store : Store effectLayout)
    (key : StateKey) (outside : key ∉ mutations.map Mutation.key) :
    applyPatch mutations store key.address = store key.address := by
  apply Patch.run_frame
  rw [lowerPatch_writeFootprint]
  intro member
  apply outside
  simp only [List.mem_toFinset, List.mem_map] at member
  obtain ⟨mutation, mem, same⟩ := member
  exact List.mem_map.mpr ⟨mutation, mem, StateKey.address_injective same⟩

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
    (pre : Store effectLayout) : Bool :=
  declaration.effects.all fun effect => effect.guardCheck pre

def Declaration.evaluate {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (pre : Store effectLayout) : Option (Store effectLayout) :=
  if declaration.guardsCheck pre = true
  then some (applyPatch declaration.patch pre)
  else none

/-- An accepted evaluation is exactly the run of the lowered guarded patch,
which is valid at the pre-store. -/
theorem Declaration.evaluate_executes {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (pre post : Store effectLayout) (evaluated : declaration.evaluate pre = some post) :
    Patch.Executes pre (lowerPatch declaration.patch pre) post := by
  by_cases guards : declaration.guardsCheck pre = true
  · simp only [Declaration.evaluate, guards, if_true, Option.some.injEq] at evaluated
    exact ⟨lowerPatch_valid _ _, evaluated⟩
  · simp [Declaration.evaluate, guards] at evaluated

/-- The derived interpreter changes nothing outside the exact derived
footprint. -/
theorem Declaration.evaluate_frame {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (pre post : Store effectLayout) (evaluated : declaration.evaluate pre = some post)
    (key : StateKey) (outside : key ∉ declaration.footprint) :
    post key.address = pre key.address := by
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
    (declaration : Declaration request.target) (pre post : Store effectLayout) : Type where
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
    (declaration : Declaration request.target) (pre : Store effectLayout) : Type where
  | accepted (post : Store effectLayout)
      (token : AuthorizedEffect (portal := portal) (authState := authState)
        declaration pre post)
  | rejected (reason : RejectReason)

/-- Executable effect admission.  The state patch exists only in `accepted`. -/
def check {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (authorization : Authorized portal authState request)
    (declaration : Declaration request.target) (pre : Store effectLayout) :
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
    {declaration : Declaration request.target} {pre : Store effectLayout} :
    CheckOutcome (portal := portal) (authState := authState) declaration pre →
      Option (Store effectLayout)
  | .accepted post _ => some post
  | .rejected _ => none

/-- Reject-before-patch: every refusal has no replacement state. -/
theorem check_rejected_no_patch {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (authorization : Authorized portal authState request)
    (declaration : Declaration request.target) (pre : Store effectLayout)
    (reason : RejectReason)
    (rejected : check authorization declaration pre = .rejected reason) :
    (check authorization declaration pre).patch? = none := by
  rw [rejected]
  rfl

/-- Every accepted token inherits the exact frame law. -/
theorem AuthorizedEffect.frame {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {declaration : Declaration request.target} {pre post : Store effectLayout}
    (token : AuthorizedEffect (portal := portal) (authState := authState)
      declaration pre post)
    (key : StateKey) (outside : key ∉ declaration.footprint) :
    post key.address = pre key.address :=
  declaration.evaluate_frame pre post token.evaluated key outside

/-- Every accepted token exposes exact, full-resource balance. -/
theorem AuthorizedEffect.balance {portal : Portal} {authState : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {declaration : Declaration request.target} {pre post : Store effectLayout}
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
    {declaration : Declaration request.target} {pre post : Store effectLayout}
    (_token : AuthorizedEffect (portal := portal) (authState := authState)
      declaration pre post)
    (replacement : ResourceId kind) (different : replacement ≠ request.target) :
    declaration.boundTarget ≠ replacement := by
  simpa using different.symm

/-! ## Poles for the lowered executor -/

namespace Example

def object : ResourceId .object := ⟨1⟩
def field : Digest := ⟨2⟩
def otherField : Digest := ⟨3⟩
def source : ResourceId .account := ⟨4⟩
def destination : ResourceId .account := ⟨5⟩
def asset : Digest := ⟨6⟩

def write (expected replacement : Int) : Declaration object :=
  { effects := [.objectWrite object field expected replacement] }

def move (amount : Int) : Declaration source :=
  { effects := [.accountMove source destination asset amount] }

/-- An absent field reads as `0`, so the guard accepts and the write allocates. -/
theorem write_absent_allocates :
    ((write 0 5).evaluate 0).map (fun post => post (StateKey.objectField object field).address) =
      some (some 5) := by
  decide

/-- Frame satisfied: a key outside the footprint is untouched. -/
theorem write_frame_outside :
    StateKey.objectField object otherField ∉ (write 0 5).footprint ∧
      ((write 0 5).evaluate 0).map
          (fun post => post (StateKey.objectField object otherField).address) =
        some none := by
  decide

/-- The frame premise is load-bearing: the footprint key does change. -/
theorem write_frame_inside_changes :
    StateKey.objectField object field ∈ (write 0 5).footprint ∧
      ((write 0 5).evaluate 0).map
          (fun post => post (StateKey.objectField object field).address) ≠
        some ((0 : Store effectLayout) (StateKey.objectField object field).address) := by
  decide

/-- A stale guard is refused before any patch runs. -/
theorem write_stale_refused : (write 1 5).evaluate 0 = none := by
  decide

/-- A move debits and credits absent balances through allocation. -/
theorem move_absent_balances :
    ((move 3).evaluate 0).map (fun post =>
        (read post (.accountBalance source asset),
          read post (.accountBalance destination asset))) =
      some (-3, 3) := by
  decide

end Example

/-- info: 'Minidregg.Theory.EffectDeclaration.Declaration.evaluate_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Declaration.evaluate_frame
/-- info: 'Minidregg.Theory.EffectDeclaration.Declaration.evaluate_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Declaration.evaluate_executes
/-- info: 'Minidregg.Theory.EffectDeclaration.Example.write_frame_inside_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.write_frame_inside_changes

end Minidregg.Theory.EffectDeclaration
