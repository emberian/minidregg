/-
# Theory.DeclaredActionLowering -- one first-order action batch, one semantic patch

This module closes the declaration half of the legacy-effect migration without
introducing an executor callback.  A batch is closed data: `create`, guarded
`write`, and exact account `move`.  Its lawful bytes, guarded patch, footprint,
full-width balance postings, eager nullifier, request commitment, and resource
charge are all projections of that one value.

Each action lowers to guarded `Store.Op`s over `EffectDeclaration.effectLayout`:
a present expected value is an `Op.write` guarded by it, an absent one is an
`Op.allocate`.  There is no second guarded-write type; the guard checker is
`Store.Patch.ValidFrom` and the post is `Store.Patch.run`.  `Accepted` retains
admission and guard validity at the sole validator-minted pre-cell.  Thus a
host may submit bytes and authority evidence, but cannot substitute a callback
or a separately interpreted replacement.

The state layout is deliberately the deployed `EffectDeclaration.effectLayout`.
This is a bounded lowering for that effect vocabulary, not a claim that every
future language can be encoded by these three constructors.
-/
import Theory.AcceptedCellEffect
import Theory.DeclaredTurn
import Theory.ResourceCost

namespace Minidregg.Theory.DeclaredActionLowering

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Closed action syntax and its guarded operations -/

/-- One action in the bounded declared language.  `move` retains both exact
representation-level expected values; absence and a stored zero are therefore
not conflated at the lowering boundary. -/
inductive Action where
  | create (key : StateKey) (initial : Int)
  | write (key : StateKey) (expected : Option Int) (replacement : Int)
  | move (source destination : ResourceId .account) (resource : Digest)
      (sourceExpected destinationExpected : Option Int) (amount : Int)
  deriving DecidableEq, Repr

/-- Raw writes are confined to the non-monetary coordinates of the exact
authorization target. Account balances are changed only by `move`. -/
def writableKeyCheck {kind : ResourceKind} (target : ResourceId kind)
    (key : StateKey) : Bool :=
  match kind, key with
  | .object, .objectField object _ => decide (object = target)
  | .program, .programCode program => decide (program = target)
  | _, _ => false

/-- The scoped ordinary-transfer discipline. A move authorizes its debited
source, has a nonnegative amount, and is funded at its sequential source read.
Mint is deliberately absent: issuer-backed mint belongs to the canonical
resource operation family, not a raw balance write. -/
def Action.admissionCheck {kind : ResourceKind} (target : ResourceId kind) :
    Action -> Bool
  | .create key _ => writableKeyCheck target key
  | .write key _ _ => writableKeyCheck target key
  | .move source _ _ sourceExpected _ amount =>
      match kind with
      | .account => decide (source = target) &&
          decide (0 <= amount) && decide (amount <= sourceExpected.getD 0)
      | _ => false

def Action.Admitted {kind : ResourceKind} (target : ResourceId kind)
    (action : Action) : Prop := action.admissionCheck target = true

/-- The guarded operation installing `replacement` at `key` when the key holds
exactly `expected`: an overwrite guarded by a present value, or an allocation
guarded by absence. -/
def guardedSet (key : StateKey) (expected : Option Int) (replacement : Int) :
    Op effectLayout :=
  match expected with
  | some before => .write () key before replacement
  | none => .allocate () key replacement

@[simp] theorem guardedSet_address (key : StateKey) (expected : Option Int)
    (replacement : Int) :
    (guardedSet key expected replacement).writeAddress? = some key.address := by
  cases expected <;> rfl

/-- The guard of `guardedSet` is exactly the expected representation-level
value (the effect layout is RAM, so no discipline side condition remains). -/
theorem guardedSet_enabled_iff (store : Store effectLayout) (key : StateKey)
    (expected : Option Int) (replacement : Int) :
    (guardedSet key expected replacement).Enabled store ↔
      store key.address = expected := by
  cases expected with
  | some before =>
      change effectLayout.discipline () = .ram ∧ store key.address = some before ↔ _
      simp
  | none =>
      change effectLayout.discipline () ≠ .rom ∧ store key.address = none ↔ _
      simp

@[simp] theorem guardedSet_apply (store : Store effectLayout) (key : StateKey)
    (expected : Option Int) (replacement : Int) :
    (guardedSet key expected replacement).apply store =
      store.set key.address (some replacement) := by
  cases expected <;> rfl

/-- The one lowering: every action is a list of guarded operations. -/
def Action.ops : Action -> Patch effectLayout
  | .create key initial => [guardedSet key none initial]
  | .write key expected replacement => [guardedSet key expected replacement]
  | .move source destination resource sourceExpected destinationExpected amount =>
      [guardedSet (.accountBalance source resource) sourceExpected
         (sourceExpected.getD 0 - amount),
       guardedSet (.accountBalance destination resource) destinationExpected
         (destinationExpected.getD 0 + amount)]

/-- A full-width posting is derived only for a move. -/
structure Posting where
  account : ResourceId .account
  resource : Digest
  amount : Int
  deriving DecidableEq, Repr

def Action.postings : Action -> List Posting
  | .move source destination resource _ _ amount =>
      [{ account := source, resource := resource, amount := -amount },
       { account := destination, resource := resource, amount := amount }]
  | _ => []

def postingSum (postings : List Posting) (resource : Digest) : Int :=
  (postings.map fun posting =>
    if posting.resource = resource then posting.amount else 0).sum

@[simp] theorem Action.postingSum_zero (action : Action) (resource : Digest) :
    postingSum action.postings resource = 0 := by
  cases action with
  | create => simp [Action.postings, postingSum]
  | write => simp [Action.postings, postingSum]
  | move source destination moved sourceExpected destinationExpected amount =>
      by_cases same : moved = resource
      · simp [Action.postings, postingSum, same]
      · simp [Action.postings, postingSum, same]

/-! ## Actual-state balance accounting for the ordered patch -/

/-- The semantic balance view retains absence in the guards but reads absent
balances as zero (`EffectDeclaration.read`) for full-width accounting. -/
def balance (store : Store effectLayout)
    (account : ResourceId .account) (resource : Digest) : Int :=
  EffectDeclaration.read store (.accountBalance account resource)

/-- The balance change one guarded operation makes at one balance key, read
from the operation's own syntax. -/
def balanceDelta : Op effectLayout → ResourceId .account → Digest → Int
  | .read _ _ _, _, _ => 0
  | .write _ key before after, account, resource =>
      if key = .accountBalance account resource then after - before else 0
  | .allocate _ key value, account, resource =>
      if key = .accountBalance account resource then value else 0
  | .free _ key before, account, resource =>
      if key = .accountBalance account resource then -before else 0

def postingDelta (postings : List Posting)
    (account : ResourceId .account) (resource : Digest) : Int :=
  (postings.map fun posting =>
    if posting.account = account ∧ posting.resource = resource then
      posting.amount else 0).sum

/-- An enabled operation changes a balance by exactly its syntactic delta. -/
theorem balance_apply (store : Store effectLayout) (op : Op effectLayout)
    (enabled : op.Enabled store) (account : ResourceId .account) (resource : Digest) :
    balance (op.apply store) account resource - balance store account resource =
      balanceDelta op account resource := by
  have other : ∀ key : StateKey, key ≠ .accountBalance account resource →
      ∀ value, read (store.set key.address value) (.accountBalance account resource) =
        EffectDeclaration.read store (.accountBalance account resource) := by
    intro key different value
    unfold EffectDeclaration.read
    rw [Store.set_ne]
    intro same
    exact different (StateKey.address_injective same).symm
  cases op with
  | read => simp [Op.apply, balanceDelta]
  | write space key before after =>
      change balance (store.set key.address (some after)) account resource -
        balance store account resource = balanceDelta (.write space key before after) account resource
      by_cases same : key = .accountBalance account resource
      · subst same
        have present : store (StateKey.accountBalance account resource).address =
            some before := enabled.2
        simp only [balance, EffectDeclaration.read, Store.set_eq, present, Option.getD_some,
          balanceDelta, if_true]
      · simp only [balance, balanceDelta, same, if_false, other key same, sub_self]
  | allocate space key value =>
      change balance (store.set key.address (some value)) account resource -
        balance store account resource = balanceDelta (.allocate space key value) account resource
      by_cases same : key = .accountBalance account resource
      · subst same
        have absent : store (StateKey.accountBalance account resource).address = none :=
          enabled.2
        simp only [balance, EffectDeclaration.read, Store.set_eq, absent, Option.getD_some,
          Option.getD_none, balanceDelta, if_true, sub_zero]
      · simp only [balance, balanceDelta, same, if_false, other key same, sub_self]
  | free space key before =>
      change balance (store.set key.address none) account resource -
        balance store account resource = balanceDelta (.free space key before) account resource
      by_cases same : key = .accountBalance account resource
      · subst same
        have present : store (StateKey.accountBalance account resource).address =
            some before := enabled.2
        simp only [balance, EffectDeclaration.read, Store.set_eq, present, Option.getD_some,
          Option.getD_none, balanceDelta, if_true, zero_sub]
      · simp only [balance, balanceDelta, same, if_false, other key same, sub_self]

theorem guardedSet_balanceDelta (key : StateKey) (expected : Option Int)
    (replacement : Int) (account : ResourceId .account) (resource : Digest) :
    balanceDelta (guardedSet key expected replacement) account resource =
      if key = .accountBalance account resource then
        replacement - expected.getD 0 else 0 := by
  cases expected <;> simp [guardedSet, balanceDelta]

/-- Every guarded step contributes its actual coordinate difference. This
telescopes across duplicate keys, including the two writes of a self-transfer. -/
theorem patch_run_balance (patch : Patch effectLayout) (store : Store effectLayout)
    (valid : Patch.ValidFrom store patch)
    (account : ResourceId .account) (resource : Digest) :
    balance (Patch.run store patch) account resource - balance store account resource =
      (patch.map fun op => balanceDelta op account resource).sum := by
  induction patch generalizing store with
  | nil => simp
  | cons op rest induction =>
      have tailDelta := induction (op.apply store) valid.2
      have headDelta := balance_apply store op valid.1 account resource
      simp only [Patch.run_cons, List.map_cons, List.sum_cons]
      omega

theorem Action.admitted_move_iff
    (target source destination : ResourceId .account) (resource : Digest)
    (sourceExpected destinationExpected : Option Int) (amount : Int) :
    (Action.move source destination resource sourceExpected destinationExpected
      amount).Admitted target ↔
      source = target ∧ 0 ≤ amount ∧ amount ≤ sourceExpected.getD 0 := by
  simp only [Action.Admitted, Action.admissionCheck, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

/-- Every valid admitted move leaves its source nonnegative. The first guard
binds solvency to the actual source read, and telescoping handles the
self-transfer case without assuming distinct endpoints. -/
theorem Action.run_move_source_nonnegative
    (target source destination : ResourceId .account) (resource : Digest)
    (sourceExpected destinationExpected : Option Int) (amount : Int)
    (store : Store effectLayout)
    (admitted : (Action.move source destination resource sourceExpected
      destinationExpected amount).Admitted target)
    (valid : Patch.ValidFrom store
      (Action.move source destination resource sourceExpected destinationExpected
        amount).ops) :
    0 ≤ balance (Patch.run store
      (Action.move source destination resource sourceExpected destinationExpected
        amount).ops) source resource := by
  have scopeFacts := (Action.admitted_move_iff target source destination resource
    sourceExpected destinationExpected amount).mp admitted
  have firstRead : store (StateKey.accountBalance source resource).address =
      sourceExpected :=
    (guardedSet_enabled_iff _ _ _ _).mp valid.1
  have readEq : balance store source resource = sourceExpected.getD 0 := by
    simp only [balance, EffectDeclaration.read, firstRead]
  have delta := patch_run_balance _ store valid source resource
  simp only [Action.ops, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    guardedSet_balanceDelta, StateKey.accountBalance.injEq, and_true,
    if_true] at delta ⊢
  have funded := scopeFacts.2.2
  split_ifs at delta <;> omega

/-- Account support is derived from an actual patch footprint, not supplied
beside the patch or captured from another declaration. -/
def balanceAccounts (footprint : Finset (Address effectLayout)) :
    Finset (ResourceId .account) :=
  footprint.biUnion fun address =>
    match address.2 with
    | .accountBalance account _ => {account}
    | _ => ∅

theorem mem_balanceAccounts {footprint : Finset (Address effectLayout)}
    {account : ResourceId .account} {resource : Digest}
    (member : (StateKey.accountBalance account resource).address ∈ footprint) :
    account ∈ balanceAccounts footprint := by
  apply Finset.mem_biUnion.mpr
  exact ⟨_, member, by simp [StateKey.address]⟩

theorem postingDelta_sum (postings : List Posting)
    (accounts : Finset (ResourceId .account))
    (covers : ∀ posting ∈ postings, posting.account ∈ accounts)
    (resource : Digest) :
    (∑ account ∈ accounts, postingDelta postings account resource) =
      postingSum postings resource := by
  induction postings with
  | nil => simp [postingDelta, postingSum]
  | cons posting rest induction =>
      have present := covers posting (by simp)
      have tailCovers : ∀ entry ∈ rest, entry.account ∈ accounts := by
        intro entry member
        exact covers entry (by simp [member])
      simp only [postingDelta, postingSum, List.map_cons, List.sum_cons,
        Finset.sum_add_distrib] at induction ⊢
      rw [induction tailCovers]
      by_cases same : posting.resource = resource
      · simp [same, present]
      · simp [same]

/-- A raw non-money write admitted under any target cannot name a balance. -/
theorem writableKey_not_account {kind : ResourceKind} (target : ResourceId kind)
    (key : StateKey) (admitted : writableKeyCheck target key = true)
    (account : ResourceId .account) (resource : Digest) :
    key ≠ .accountBalance account resource := by
  intro same
  subst key
  cases kind <;> simp [writableKeyCheck] at admitted

theorem Action.ops_balanceDelta {kind : ResourceKind}
    (target : ResourceId kind) (action : Action) (admitted : action.Admitted target)
    (account : ResourceId .account) (resource : Digest) :
    (action.ops.map fun op => balanceDelta op account resource).sum =
      postingDelta action.postings account resource := by
  cases action with
  | create key initial =>
      have outside := writableKey_not_account target key admitted account resource
      simp [Action.ops, Action.postings, guardedSet_balanceDelta, postingDelta, outside]
  | write key expected replacement =>
      have outside := writableKey_not_account target key admitted account resource
      simp [Action.ops, Action.postings, guardedSet_balanceDelta, postingDelta, outside]
  | move source destination moved sourceExpected destinationExpected amount =>
      simp only [Action.ops, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, guardedSet_balanceDelta,
        Action.postings, postingDelta]
      simp only [StateKey.accountBalance.injEq]
      split_ifs <;> omega

theorem Action.posting_key_mem (action : Action) (posting : Posting)
    (member : posting ∈ action.postings) :
    (StateKey.accountBalance posting.account posting.resource).address ∈
      Patch.writeFootprint action.ops := by
  cases action with
  | create => simp [Action.postings] at member
  | write => simp [Action.postings] at member
  | move source destination resource sourceExpected destinationExpected amount =>
      simp only [Action.postings, List.mem_cons, List.not_mem_nil, or_false] at member
      rw [Patch.mem_writeFootprint_iff]
      rcases member with rfl | rfl
      · exact ⟨_, List.mem_cons_self, guardedSet_address _ _ _⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, guardedSet_address _ _ _⟩

/-! ## Lawful first-order bytes -/

def keyCode : StateKey -> Nat
  | .objectField object field =>
      Nat.pair 0 (Nat.pair object.value field.value)
  | .accountBalance account resource =>
      Nat.pair 1 (Nat.pair account.value resource.value)
  | .programCode program => Nat.pair 2 program.value

def keyOfCode (code : Nat) : Option StateKey :=
  let tagged := Nat.unpair code
  match tagged.1 with
  | 0 =>
      let parts := Nat.unpair tagged.2
      some (.objectField ⟨parts.1⟩ ⟨parts.2⟩)
  | 1 =>
      let parts := Nat.unpair tagged.2
      some (.accountBalance ⟨parts.1⟩ ⟨parts.2⟩)
  | 2 => some (.programCode ⟨tagged.2⟩)
  | _ => none

@[simp] theorem keyOfCode_keyCode (key : StateKey) :
    keyOfCode (keyCode key) = some key := by
  cases key <;> simp [keyCode, keyOfCode]

def optionIntCode : Option Int -> Nat
  | none => 0
  | some value => EffectDeclaration.encodeInt value + 1

def optionIntOfCode : Nat -> Option (Option Int)
  | 0 => some none
  | code + 1 => some (some (decodeInt code))

@[simp] theorem optionIntOfCode_optionIntCode (value : Option Int) :
    optionIntOfCode (optionIntCode value) = some value := by
  cases value <;> simp [optionIntCode, optionIntOfCode]

def Action.code : Action -> Nat
  | .create key initial =>
      Nat.pair 0 (Nat.pair (keyCode key) (EffectDeclaration.encodeInt initial))
  | .write key expected replacement =>
      Nat.pair 1 (Nat.pair (keyCode key)
        (Nat.pair (optionIntCode expected)
          (EffectDeclaration.encodeInt replacement)))
  | .move source destination resource sourceExpected destinationExpected amount =>
      Nat.pair 2
        (Nat.pair source.value
          (Nat.pair destination.value
            (Nat.pair resource.value
              (Nat.pair (optionIntCode sourceExpected)
                (Nat.pair (optionIntCode destinationExpected)
                  (EffectDeclaration.encodeInt amount))))))

def actionOfCode (code : Nat) : Option Action := do
  let tagged := Nat.unpair code
  match tagged.1 with
  | 0 =>
      let parts := Nat.unpair tagged.2
      let key <- keyOfCode parts.1
      pure (.create key (decodeInt parts.2))
  | 1 =>
      let keyRest := Nat.unpair tagged.2
      let expectedReplacement := Nat.unpair keyRest.2
      let key <- keyOfCode keyRest.1
      let expected <- optionIntOfCode expectedReplacement.1
      pure (.write key expected (decodeInt expectedReplacement.2))
  | 2 =>
      let sourceRest := Nat.unpair tagged.2
      let destinationRest := Nat.unpair sourceRest.2
      let resourceRest := Nat.unpair destinationRest.2
      let sourceExpectedRest := Nat.unpair resourceRest.2
      let destinationExpectedAmount := Nat.unpair sourceExpectedRest.2
      let sourceExpected <- optionIntOfCode sourceExpectedRest.1
      let destinationExpected <- optionIntOfCode destinationExpectedAmount.1
      pure (.move ⟨sourceRest.1⟩ ⟨destinationRest.1⟩ ⟨resourceRest.1⟩
        sourceExpected destinationExpected (decodeInt destinationExpectedAmount.2))
  | _ => none

@[simp] theorem actionOfCode_code (action : Action) :
    actionOfCode action.code = some action := by
  cases action <;> simp [Action.code, actionOfCode]

def actionsCode : List Action -> Nat
  | [] => 0
  | action :: rest => Nat.pair action.code (actionsCode rest) + 1

def actionsOfCode : Nat -> Option (List Action)
  | 0 => some []
  | code + 1 => do
      let parts := Nat.unpair code
      let action <- actionOfCode parts.1
      let rest <- actionsOfCode parts.2
      pure (action :: rest)
termination_by code => code
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

@[simp] theorem actionsOfCode_actionsCode (actions : List Action) :
    actionsOfCode (actionsCode actions) = some actions := by
  induction actions with
  | nil => simp [actionsCode, actionsOfCode]
  | cons action rest induction =>
      simp [actionsCode, actionsOfCode, induction]

def resourceKindTag : ResourceKind -> Nat
  | .object => 0
  | .account => 1
  | .program => 2

/-- One exact authority target owns a batch.  Its bytes include that target,
kind, pre-root, nonce, and the complete ordered action list. -/
structure Declaration {kind : ResourceKind} (target : ResourceId kind) where
  schemaVersion : Nat
  expectedPreRoot : Digest
  nonce : Nat
  actions : List Action
  deriving DecidableEq, Repr

/-- Every member of this single-authority batch is scoped independently.
Cross-authority work must use separate admitted hyperedge incidences. -/
def Declaration.admissionCheck {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Bool :=
  declaration.actions.all (Action.admissionCheck target)

def Declaration.Admitted {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Prop :=
  declaration.admissionCheck = true

def Declaration.code {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Nat :=
  Nat.pair (resourceKindTag kind)
    (Nat.pair target.value
      (Nat.pair declaration.schemaVersion
        (Nat.pair declaration.expectedPreRoot.value
          (Nat.pair declaration.nonce (actionsCode declaration.actions)))))

def declarationOfCode {kind : ResourceKind} (target : ResourceId kind)
    (code : Nat) : Option (Declaration target) := do
  let kindRest := Nat.unpair code
  let targetRest := Nat.unpair kindRest.2
  if kindRest.1 != resourceKindTag kind then none
  else if targetRest.1 != target.value then none
  else
    let schemaRest := Nat.unpair targetRest.2
    let rootRest := Nat.unpair schemaRest.2
    let nonceActions := Nat.unpair rootRest.2
    let actions <- actionsOfCode nonceActions.2
    pure
      { schemaVersion := schemaRest.1
        expectedPreRoot := ⟨rootRest.1⟩
        nonce := nonceActions.1
        actions := actions }

@[simp] theorem declarationOfCode_code {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target) :
    declarationOfCode target declaration.code = some declaration := by
  cases kind <;> simp [Declaration.code, declarationOfCode, resourceKindTag]

def declarationCodec {kind : ResourceKind} (target : ResourceId kind) :
    LawfulCodec (Declaration target) where
  encode := fun declaration => List.replicate (declaration.code + 1) 0
  decode := fun bytes =>
    if bytes.all fun byte => byte == 0 then
      declarationOfCode target (bytes.length - 1)
    else none
  decode_encode := by
    intro declaration
    simp only [List.all_eq_true, List.mem_replicate, beq_iff_eq,
      List.length_replicate, Nat.add_sub_cancel]
    simp

/-! ## The sole semantic lowering -/

/-- The one guarded patch of a batch. -/
def Declaration.patch {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Patch effectLayout :=
  declaration.actions.flatMap Action.ops

/-- The executable checker: scoped admission, then every guard in sequence.
Its post is the one patch run; there is no second interpreter. -/
def Declaration.run {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (store : Store effectLayout) :
    Option (Store effectLayout) :=
  if declaration.admissionCheck = true ∧ Patch.ValidFrom store declaration.patch then
    some (Patch.run store declaration.patch)
  else none

def Declaration.postings {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List Posting :=
  declaration.actions.flatMap Action.postings

theorem Declaration.admitted_iff {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) :
    declaration.Admitted ↔
      ∀ action ∈ declaration.actions, action.Admitted target := by
  simp [Declaration.Admitted, Declaration.admissionCheck, Action.Admitted]

theorem Declaration.run_eq_some_iff {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (store post : Store effectLayout) :
    declaration.run store = some post ↔
      declaration.Admitted ∧ Patch.ValidFrom store declaration.patch ∧
        post = Patch.run store declaration.patch := by
  unfold Declaration.run Declaration.Admitted
  split_ifs with checked
  · simp only [Option.some.injEq]
    constructor
    · intro exact
      exact ⟨checked.1, checked.2, exact.symm⟩
    · intro facts
      exact facts.2.2.symm
  · simp only [false_iff]
    intro facts
    exact checked ⟨facts.1, facts.2.1⟩

theorem actions_ops_balanceDelta {kind : ResourceKind}
    (target : ResourceId kind) (actions : List Action)
    (admitted : ∀ action ∈ actions, action.Admitted target)
    (account : ResourceId .account) (resource : Digest) :
    ((actions.flatMap Action.ops).map fun op =>
        balanceDelta op account resource).sum =
      postingDelta (actions.flatMap Action.postings) account resource := by
  induction actions with
  | nil => simp [postingDelta]
  | cons action rest induction =>
      have headAdmitted := admitted action (by simp)
      have tailAdmitted : ∀ entry ∈ rest, entry.Admitted target := by
        intro entry member
        exact admitted entry (by simp [member])
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [Action.ops_balanceDelta target action headAdmitted,
        induction tailAdmitted]
      simp [postingDelta]

/-- The ordered patch's actual coordinate difference is exactly the declared
posting delta for every account and full resource identifier. -/
theorem Declaration.run_balance {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target)
    (store post : Store effectLayout)
    (run : declaration.run store = some post)
    (account : ResourceId .account) (resource : Digest) :
    balance post account resource - balance store account resource =
      postingDelta declaration.postings account resource := by
  obtain ⟨admitted, valid, rfl⟩ := (declaration.run_eq_some_iff store post).mp run
  rw [patch_run_balance declaration.patch store valid]
  exact actions_ops_balanceDelta target declaration.actions
    (declaration.admitted_iff.mp admitted) account resource

theorem Declaration.posting_account_mem {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (posting : Posting) (member : posting ∈ declaration.postings) :
    posting.account ∈ balanceAccounts (Patch.writeFootprint declaration.patch) := by
  apply mem_balanceAccounts (resource := posting.resource)
  obtain ⟨action, actionMember, postingMember⟩ := List.mem_flatMap.mp member
  have keyMember := action.posting_key_mem posting postingMember
  rw [Patch.mem_writeFootprint_iff] at keyMember ⊢
  obtain ⟨op, opMember, written⟩ := keyMember
  exact ⟨op, List.mem_flatMap.mpr ⟨action, actionMember, opMember⟩, written⟩

theorem postingSum_append (left right : List Posting) (resource : Digest) :
    postingSum (left ++ right) resource =
      postingSum left resource + postingSum right resource := by
  simp [postingSum, List.map_append, List.sum_append]

/-- Every complete resource namespace is conserved by construction. -/
theorem Declaration.postingSum_zero {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (resource : Digest) :
    postingSum declaration.postings resource = 0 := by
  change postingSum (declaration.actions.flatMap Action.postings) resource = 0
  induction declaration.actions with
  | nil => rfl
  | cons action rest induction =>
      rw [List.flatMap_cons, postingSum_append,
        Action.postingSum_zero, induction, add_zero]

/-- Domain-separated model commitment to the complete lawful bytes. -/
def digestDeclaration {kind : ResourceKind} {target : ResourceId kind}
    (domain : Nat) (declaration : Declaration target) : Digest :=
  ⟨Nat.pair domain declaration.code⟩

def argsDigest {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Digest :=
  digestDeclaration 30 declaration

def effectDigest {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Digest :=
  digestDeclaration 31 declaration

/-- Every charged coordinate is determined from the same declaration. -/
def exactCharge {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Charge :=
  fun lane =>
    match lane with
    | .incidences => 1
    | .turnBytes => (declarationCodec target).encode declaration |>.length
    | .memoryTouches => (Patch.writeFootprint declaration.patch).card
    | .storageBytes => declaration.patch.length
    | .sideEffectCount => declaration.actions.length
    | .feeDebit => declaration.actions.foldl (fun total action =>
        match action with
        | .move _ _ _ _ _ amount => total + amount.natAbs
        | _ => total) 0
    | _ => 0

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by simp

/-- Scoped admission and ordered guard success concern the exact canonical
pre-cell used by this family's receiving constructor. -/
structure ValidAt {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    (pre : Materialized M) (declaration : Declaration target) : Prop where
  rootExact : declaration.expectedPreRoot = pre.root
  admitted : declaration.Admitted
  guards : Patch.ValidFrom pre.logical declaration.patch

/-- The executable checker accepts exactly at a valid pre-cell, with the one
patch run as its post. -/
theorem ValidAt.run {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {pre : Materialized M} {declaration : Declaration target}
    (valid : ValidAt pre declaration) :
    declaration.run pre.logical = some (Patch.run pre.logical declaration.patch) :=
  (declaration.run_eq_some_iff _ _).mpr ⟨valid.admitted, valid.guards, rfl⟩

/-! ## Complete request and accepted lowering -/

structure RequestContext where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch
  policyRevision : PolicyRevision

def RequestContext.request {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target) : Request kind where
  domain := context.domain
  semantics := context.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := target
  verb := match kind with
    | .object => .mutateObject
    | .account => .transfer
    | .program => .installProgram
  argsDigest := argsDigest declaration
  effectsDigest := effectDigest declaration
  nonce := declaration.nonce
  height := context.height
  preStateRoot := declaration.expectedPreRoot
  policyId := context.policyId
  policyEpoch := context.policyEpoch
  policyRevision := context.policyRevision
  cost := exactCharge declaration .feeDebit

def family {kind : ResourceKind} (target : ResourceId kind)
    (context : RequestContext)
    {M : Materializer effectLayout Digest}
    (pre : Materialized M) :
    SemanticEffectFamily effectLayout M Nat where
  Declaration := Declaration target
  declarationCodec := declarationCodec target
  pre := pre
  request := fun declaration => ⟨kind, context.request declaration⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => PLift (ValidAt pre declaration)
  Postcondition := fun declaration _ post =>
    declaration.patch.ResultAt pre.logical post
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.nonce
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ decision => decision = .sealed

theorem patch_validated {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {pre : Materialized M} {declaration : Declaration target}
    (valid : ValidAt pre declaration) :
    ValidatedPatch M pre declaration.expectedPreRoot declaration.patch := by
  obtain ⟨validated, _⟩ := validate_accepts M pre declaration.expectedPreRoot
    declaration.patch valid.rootExact valid.guards
  exact validated

/-- Positive lowering carrier with scoped admission and guard/post equality
retained by the generic accepted effect's family evidence. -/
structure Accepted {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    (portal : Portal) (authState : AuthState)
    (context : RequestContext) (pre : Materialized M)
    (declaration : Declaration target) : Type where
  cellEffect : AcceptedCellEffect (portal := portal) (authState := authState)
    (family target context pre) (context.request declaration) pre declaration ()

/-- Validation lives on the family face, so a generic accepted-effect consumer
cannot discard it when the wrapper is projected away. -/
def Accepted.valid {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    ValidAt pre declaration := accepted.cellEffect.modeEvidence.down

def accept {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M}
    {declaration : Declaration target}
    (authorization : Authorized portal authState (context.request declaration))
    (valid : ValidAt pre declaration) :
    Accepted portal authState context pre declaration where
  cellEffect :=
    { authorization := authorization
      preStateBound := rfl
      requestBound := rfl
      effectsDigestBound := rfl
      modeEvidence := PLift.up valid
      validated := patch_validated valid
      postcondition := (patch_validated valid).resultAt
      disclosure := .sealed
      disclosureAllowed := rfl }

/-- Executable admission computes the common scoped check and sequential
guards before constructing the existing accepted carrier. Its post is always
the canonical patch application, never the returned host proposal. -/
def admit {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    (pre : Materialized M) (declaration : Declaration target)
    (authorization : Authorized portal authState (context.request declaration)) :
    Option (Accepted portal authState context pre declaration) :=
  if root : declaration.expectedPreRoot = pre.root then
    if checked : declaration.admissionCheck = true ∧
        Patch.ValidFrom pre.logical declaration.patch then
      some (accept authorization
        { rootExact := root, admitted := checked.1, guards := checked.2 })
    else none
  else none

/-- The executable constructor is complete for the same family validity
evidence consumed by the proof-relevant lowering. -/
theorem admit_eq_some {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (authorization : Authorized portal authState (context.request declaration))
    (valid : ValidAt pre declaration) :
    admit pre declaration authorization = some (accept authorization valid) := by
  simp only [admit, dif_pos valid.rootExact,
    dif_pos (show declaration.admissionCheck = true ∧
      Patch.ValidFrom pre.logical declaration.patch from ⟨valid.admitted, valid.guards⟩)]

theorem Accepted.admitted {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration) :
    declaration.Admitted :=
  accepted.valid.admitted

/-- The accepted canonical post, rather than a separately asserted balance
vector, realizes every declared full-width coordinate delta. -/
theorem Accepted.balance_delta {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration)
    (account : ResourceId .account) (resource : Digest) :
    balance accepted.cellEffect.prepared.post.logical account resource -
        balance pre.logical account resource =
      postingDelta declaration.postings account resource :=
  declaration.run_balance _ _ accepted.valid.run account resource

theorem Accepted.conserves {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration)
    (resource : Digest) :
    (∑ account ∈ balanceAccounts (Patch.writeFootprint declaration.patch),
      (balance accepted.cellEffect.prepared.post.logical account resource -
        balance pre.logical account resource)) = 0 := by
  simp_rw [accepted.balance_delta]
  rw [postingDelta_sum declaration.postings _ declaration.posting_account_mem]
  exact declaration.postingSum_zero resource

/-- Accounts absent from the complete posting support cannot be silently
changed outside the conservation sum. -/
theorem Accepted.unposted_account_unchanged {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (accepted : Accepted portal authState context pre declaration)
    (account : ResourceId .account) (resource : Digest)
    (outside : ∀ posting ∈ declaration.postings, posting.account ≠ account) :
    balance accepted.cellEffect.prepared.post.logical account resource =
      balance pre.logical account resource := by
  have delta := accepted.balance_delta account resource
  have zero : postingDelta declaration.postings account resource = 0 := by
    apply List.sum_eq_zero
    intro value member
    obtain ⟨posting, postingMember, rfl⟩ := List.mem_map.mp member
    simp [outside posting postingMember]
  rw [zero] at delta
  omega

theorem no_accepted_of_inadmissible {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (inadmissible : declaration.admissionCheck = false) :
    IsEmpty (Accepted portal authState context pre declaration) :=
  ⟨fun accepted => by
    have admitted := accepted.admitted
    simp [Declaration.Admitted, inadmissible] at admitted⟩

/-- The public family face retains the same exact-pre guard proof. Receiving
code constructs both occurrences of `pre` from one reopened canonical cell. -/
theorem cellEffect_valid {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    {request : Request kind}
    (effect : AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :
    ValidAt pre declaration := effect.modeEvidence.down

/-- The family now derives the complete request from source data, so generic
consumers retain the same authority target rather than only its effect digest. -/
theorem cellEffect_target_exact {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    {request : Request kind}
    (effect : AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :
    request.target.value = target.value :=
  effect.request_projection (fun packed => packed.2.target.value)

theorem no_cellEffect_of_wrong_target {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    {request : Request kind} (wrong : request.target.value ≠ target.value) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :=
  ⟨fun effect => wrong (cellEffect_target_exact effect)⟩

theorem no_cellEffect_of_inadmissible {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    {request : Request kind}
    (inadmissible : declaration.admissionCheck = false) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :=
  ⟨fun effect => by
    have admitted := (cellEffect_valid effect).admitted
    simp [Declaration.Admitted, inadmissible] at admitted⟩

theorem no_cellEffect_of_guard_mismatch {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    {request : Request kind}
    (mismatch : declaration.run pre.logical = none) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :=
  ⟨fun effect => by
    have exactPost := (cellEffect_valid effect).run
    rw [mismatch] at exactPost
    simp at exactPost⟩

theorem no_accepted_of_guard_mismatch {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (mismatch : declaration.run pre.logical = none) :
    IsEmpty (Accepted portal authState context pre declaration) :=
  ⟨fun accepted => by
    have exactPost := accepted.valid.run
    rw [mismatch] at exactPost
    simp at exactPost⟩

theorem no_cellEffect_of_wrong_digest {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (request : Request kind)
    (wrong : request.effectsDigest ≠ effectDigest declaration) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :=
  ⟨fun accepted => wrong accepted.effectsDigestBound⟩

theorem no_cellEffect_of_stale_root {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (request : Request kind) (stale : request.preStateRoot ≠ pre.root) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target context pre) request pre declaration ()) :=
  ⟨fun accepted => stale accepted.preRootBound⟩

/-! ## Executable admission teeth, without evaluating the unary wire codec -/

namespace ScopeWitness

def source : ResourceId .account := ⟨1⟩
def destination : ResourceId .account := ⟨2⟩
def asset : Digest := ⟨3⟩

def balances : Store effectLayout :=
  ((0 : Store effectLayout).set (StateKey.accountBalance source asset).address
    (some (7 : Int))).set (StateKey.accountBalance destination asset).address
      (some (0 : Int))

def batch (actions : List Action) : Declaration source where
  schemaVersion := 1
  expectedPreRoot := ⟨0⟩
  nonce := 1
  actions := actions

def object : ResourceId .object := ⟨4⟩
def otherObject : ResourceId .object := ⟨5⟩
def program : ResourceId .program := ⟨6⟩
def otherProgram : ResourceId .program := ⟨7⟩

theorem different_object_write_refused :
    (Action.write (.objectField otherObject asset) none 1).admissionCheck object = false := by
  decide

theorem object_to_program_write_refused :
    (Action.write (.programCode program) none 1).admissionCheck object = false := by decide

theorem different_program_write_refused :
    (Action.write (.programCode otherProgram) none 1).admissionCheck program = false := by decide

theorem program_to_balance_write_refused :
    (Action.write (.accountBalance source asset) (some 7) 100).admissionCheck program =
      false := by decide

theorem raw_balance_write_refused :
    (batch [.write (.accountBalance source asset) (some 7) 100]).run balances = none := by
  decide

theorem raw_balance_create_refused :
    (batch [.create (.accountBalance destination asset) 100]).run balances = none := by
  decide

theorem different_source_refused :
    (batch [.move destination source asset (some 7) (some 0) 4]).run balances = none := by
  decide

theorem negative_amount_refused :
    (batch [.move source destination asset (some 7) (some 0) (-1)]).run balances = none := by
  decide

theorem unfunded_move_refused :
    (batch [.move source destination asset (some 7) (some 0) 8]).run balances = none := by
  decide

/-- A self-transfer's credit guard observes the debit's result, not a second
copy of the initial balance. The net coordinate change is zero. -/
theorem self_transfer_sequential :
    ((batch [.move source source asset (some 7) (some 3) 4]).run balances).map
      (fun post => balance post source asset) = some 7 := by
  decide

theorem self_transfer_stale_credit_refused :
    (batch [.move source source asset (some 7) (some 7) 4]).run balances = none := by
  decide

theorem sequential_moves :
    ((batch
      [.move source destination asset (some 7) (some 0) 4,
       .move source destination asset (some 3) (some 4) 3]).run balances).map
        (fun post => (balance post source asset, balance post destination asset)) =
      some (0, 7) := by
  decide

theorem sequential_stale_source_refused :
    (batch
      [.move source destination asset (some 7) (some 0) 4,
       .move source destination asset (some 7) (some 4) 3]).run balances = none := by
  decide

/-- Presence participates in the guard even when the semantic balance is zero. -/
theorem absent_and_zero_differ :
    (batch [.move source destination asset (some 7) none 4]).run balances = none := by
  decide

theorem missing_destination_can_receive :
    ((batch [.move source destination asset (some 7) none 4]).run
      ((0 : Store effectLayout).set (StateKey.accountBalance source asset).address
        (some (7 : Int)))).map
          (fun post => (balance post source asset, balance post destination asset)) =
      some (3, 4) := by
  decide

end ScopeWitness

/-! ## A narrow, checked legacy correspondence -/

/-- A legacy account move lowers to the same two full-width postings.  This is
the meaningful old path this bounded language subsumes; it does not claim an
adapter for arbitrary host languages. -/
def ofLegacyMove (source destination : ResourceId .account) (resource : Digest)
    (sourceExpected destinationExpected : Option Int) (amount : Int) : Action :=
  .move source destination resource sourceExpected destinationExpected amount

@[simp] theorem ofLegacyMove_postings
    (source destination : ResourceId .account) (resource : Digest)
    (sourceExpected destinationExpected : Option Int) (amount : Int) :
    (ofLegacyMove source destination resource sourceExpected
      destinationExpected amount).postings =
      [{ account := source, resource := resource, amount := -amount },
       { account := destination, resource := resource, amount := amount }] := rfl

/-! ## Axiom audit for conservation, the family boundary, and aliasing teeth -/

/-- info: 'Minidregg.Theory.DeclaredActionLowering.Declaration.run_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Declaration.run_balance
/-- info: 'Minidregg.Theory.DeclaredActionLowering.Action.run_move_source_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Action.run_move_source_nonnegative
/-- info: 'Minidregg.Theory.DeclaredActionLowering.Accepted.conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Accepted.conserves
/-- info: 'Minidregg.Theory.DeclaredActionLowering.Accepted.unposted_account_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Accepted.unposted_account_unchanged
/-- info: 'Minidregg.Theory.DeclaredActionLowering.no_cellEffect_of_inadmissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_cellEffect_of_inadmissible
/-- info: 'Minidregg.Theory.DeclaredActionLowering.no_cellEffect_of_guard_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_cellEffect_of_guard_mismatch
/-- info: 'Minidregg.Theory.DeclaredActionLowering.no_cellEffect_of_wrong_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_cellEffect_of_wrong_target
/-- info: 'Minidregg.Theory.DeclaredActionLowering.ScopeWitness.self_transfer_sequential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScopeWitness.self_transfer_sequential
/-- info: 'Minidregg.Theory.DeclaredActionLowering.ScopeWitness.self_transfer_stale_credit_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScopeWitness.self_transfer_stale_credit_refused
/-- info: 'Minidregg.Theory.DeclaredActionLowering.ScopeWitness.sequential_moves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScopeWitness.sequential_moves
/-- info: 'Minidregg.Theory.DeclaredActionLowering.ScopeWitness.sequential_stale_source_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScopeWitness.sequential_stale_source_refused

end Minidregg.Theory.DeclaredActionLowering
