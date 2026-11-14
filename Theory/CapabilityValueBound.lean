/-
# Theory.CapabilityValueBound -- the value bound a capability carries, for every debit

A capability's scope bounds a request three ways (`Theory.TypedAuthorization.Scope`): its
`targets`, its `verbs` and `maxCost`, a ceiling on `Request.cost`. `Request.cost` is a size or
a fee: for most receivers the encoded command's length, for a Book fee its amount, for an
ordinary Book transfer zero (`CanonicalResourceKernel.Operation.feeDebit`). It is not the value a
debit moves, so `maxCost` is not a value bound.

The scope's value bound is `maxDelta` on the field `CellField.balance asset`, with `fields`
naming which balances the capability may move at all. This module states that bound once, for
any list of Book operations and any account they debit, so that every receiver that debits an
account under a presented capability checks the same thing.

## Definitions

* `debits operations account` -- the postings of `operations` whose source is `account`.
* `grossDebit operations account asset` -- the sum of their amounts in `asset`. Gross: a credit
  to the same account in the same batch does not reduce it (`credit_does_not_offset`).
* `debitFootprint operations account` -- the `Footprint` a scope judges: the touched balance
  fields and, on each, minus the gross debit.
* `ValueBound scope operations account` -- `scope.FieldsCover` of that footprint.
* `check` -- the decision, with the refusal named: `fieldNotNamed asset` or
  `maxDeltaExceeded asset debited`.
* `BatchBounded presented operations` -- the statement for one admitted batch: every operation's
  source has a presented capability whose scope bounds the batch's gross debit of that source.

* `StrictBound cap operations account` -- what a receiver requires: `ValueBound` of the
  capability's scope, and, if the capability is delegated, a `maxDelta` bound on every debited
  balance (`BoundsSet`). Decided by `strictCheck`; the extra refusal is
  `missingBalanceBound asset`.
* `Presented capability operations account` -- the receiver's form over its authorization
  evidence, decided by `presentedCheck`.
* `DebitsBounded cap footprint` -- the missing-bound condition for a receiver that judges a leg
  by its `Footprint` (the resource-transaction path): a delegated capability sets a bound on
  every balance the footprint lowers. `BoundsSet.debitsBounded` relates it to the operation form.

## What an absent bound means

`maxDelta` is a set of bounds and the empty set bounds nothing; `fields = none` names every
field (`TypedAuthorization` §2a). So a SCOPE that names no field set and carries no `balance`
bound is unbounded in value (`valueBound_of_unrestricted`). A root capability keeps that
reading: its holder owns the account. A delegated capability (`parent ≠ none`) does not: it
must set a bound on every balance it debits, fees included, or the debit is refused
`missingBalanceBound` (`BoundsSet`). Only the lineage gives the exemption; holding an owner
grant does not. A written bound cannot be loosened by a descendant (`valueBound_of_narrows`).

The bound limits ONE batch (one admitted turn). It is not a cumulative allowance: repeated
turns, each within the bound, can together move more than the bound.

## Theorems

* `valueBound_iff` -- the statement in plain terms: every debited asset's balance is named,
  and the gross debit is within every bound the scope sets on it.
* `check_ok_iff`, `check_fieldNotNamed`, `check_maxDeltaExceeded` -- the decision and both
  refusals.
* `valueBound_of_unrestricted`, `valueBound_of_narrows`, `valueBound_of_no_debit`.
* `batchBounded_gross` -- under `BatchBounded`, each debited account's gross debit in an asset
  is within every bound its presented capability sets.
* `Witness` -- satisfiable, teeth and premise inhabitation, as data.
-/
module

public import Theory.CanonicalResourceKernel
public import Theory.ExceptDecidableEq
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Theory.CapabilityValueBound

open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## The gross debit of an account -/

/-- The postings of `operations` that debit `account`. -/
def debits (operations : List Operation) (account : AccountId) : List Posting :=
  (operations.map Operation.posting).filter fun posting => decide (posting.source = account)

/-- The gross amount `operations` debit from `account` in `asset`. -/
def grossDebit (operations : List Operation) (account : AccountId) (asset : AssetId) : Nat :=
  (((debits operations account).filter fun posting => decide (posting.asset = asset)).map
    Posting.amount).sum

/-- The assets in which `operations` debit `account`, in order, with repeats. -/
def debitAssetList (operations : List Operation) (account : AccountId) : List AssetId :=
  (debits operations account).map Posting.asset

/-- The assets in which `operations` debit `account`. -/
def debitAssets (operations : List Operation) (account : AccountId) : Finset AssetId :=
  (debitAssetList operations account).toFinset

/-- What a scope judges of a debit: the balance fields the account's own postings touch, and
on each, minus the gross debit. -/
def debitFootprint (operations : List Operation) (account : AccountId) : Footprint where
  touched := (debitAssets operations account).image CellField.balance
  delta := fun field => match field with
    | .balance asset => -(Int.ofNat (grossDebit operations account asset))
    | _ => 0

/-- **The value bound.** The scope names every balance `operations` debit from `account` and
bounds each gross debit. -/
def ValueBound {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) : Prop :=
  scope.FieldsCover (debitFootprint operations account)

instance {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) : Decidable (ValueBound scope operations account) := by
  unfold ValueBound
  infer_instance

theorem natAbs_debit (amount : Nat) : (-(Int.ofNat amount)).natAbs = amount := by
  rw [Int.natAbs_neg]
  rfl

/-- **The statement in plain terms.** -/
theorem valueBound_iff {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) :
    ValueBound scope operations account ↔
      ∀ asset ∈ debitAssets operations account,
        CellField.NamedBy scope.fields (.balance asset) ∧
          ∀ bound, (CellField.balance asset, bound) ∈ scope.maxDelta →
            grossDebit operations account asset ≤ bound := by
  constructor
  · intro covered asset member
    obtain ⟨named, within⟩ := covered (.balance asset) (Finset.mem_image_of_mem _ member)
    refine ⟨named, fun bound bounded => ?_⟩
    have limit := within (.balance asset, bound) bounded rfl
    change (-(Int.ofNat (grossDebit operations account asset))).natAbs ≤ bound at limit
    rwa [natAbs_debit] at limit
  · intro plain field touched
    obtain ⟨asset, member, rfl⟩ := Finset.mem_image.mp touched
    obtain ⟨named, within⟩ := plain asset member
    refine ⟨named, ?_⟩
    rintro ⟨boundField, bound⟩ bounded same
    change boundField = CellField.balance asset at same
    subst same
    change (-(Int.ofNat (grossDebit operations account asset))).natAbs ≤ bound
    rw [natAbs_debit]
    exact within bound bounded

/-! ## The decision, with the refusal named -/

inductive Refusal where
  /-- The scope's `fields` do not name the balance of `asset`. -/
  | fieldNotNamed (asset : AssetId)
  /-- The gross debit `debited` of `asset` exceeds a bound the scope sets on its balance. -/
  | maxDeltaExceeded (asset : AssetId) (debited : Nat)
  /-- The capability is delegated and its scope sets no `maxDelta` bound on the balance of
  `asset`, which the operations debit. -/
  | missingBalanceBound (asset : AssetId)
  deriving DecidableEq, Repr

/-- The refusal one debited asset earns, if any. -/
def refusalAt {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) (asset : AssetId) : Option Refusal :=
  if CellField.NamedBy scope.fields (.balance asset) then
    if CellField.WithinBounds scope.maxDelta (.balance asset)
        (-(Int.ofNat (grossDebit operations account asset))) then none
    else some (.maxDeltaExceeded asset (grossDebit operations account asset))
  else some (.fieldNotNamed asset)

/-- The check every debiting receiver runs: the first debited asset, in posting order, that
the scope does not name or bounds below its gross debit refuses, by name. -/
def check {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) : Except Refusal Unit :=
  match (debitAssetList operations account).findSome? (refusalAt scope operations account) with
  | none => .ok ()
  | some refusal => .error refusal

theorem refusalAt_eq_none_iff {kind : ResourceKind} (scope : Scope kind)
    (operations : List Operation) (account : AccountId) (asset : AssetId) :
    refusalAt scope operations account asset = none ↔
      CellField.NamedBy scope.fields (.balance asset) ∧
        CellField.WithinBounds scope.maxDelta (.balance asset)
          (-(Int.ofNat (grossDebit operations account asset))) := by
  unfold refusalAt
  by_cases named : CellField.NamedBy scope.fields (.balance asset)
  · by_cases within : CellField.WithinBounds scope.maxDelta (.balance asset)
        (-(Int.ofNat (grossDebit operations account asset)))
    · rw [if_pos named, if_pos within]
      exact iff_of_true rfl ⟨named, within⟩
    · rw [if_pos named, if_neg within]
      exact iff_of_false (by simp) (fun both => within both.2)
  · rw [if_neg named]
    exact iff_of_false (by simp) (fun both => named both.1)

/-- **The check decides the value bound.** -/
theorem check_ok_iff {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) :
    check scope operations account = .ok () ↔ ValueBound scope operations account := by
  constructor
  · intro ok
    unfold check at ok
    split at ok
    next none =>
      intro field touched
      obtain ⟨asset, member, rfl⟩ := Finset.mem_image.mp touched
      have listed : asset ∈ debitAssetList operations account := List.mem_toFinset.mp member
      exact (refusalAt_eq_none_iff scope operations account asset).mp
        (List.findSome?_eq_none_iff.mp none asset listed)
    next => cases ok
  · intro bounded
    have none : (debitAssetList operations account).findSome?
        (refusalAt scope operations account) = none :=
      List.findSome?_eq_none_iff.mpr fun asset listed =>
        (refusalAt_eq_none_iff scope operations account asset).mpr
          (bounded (.balance asset) (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr listed)))
    unfold check
    rw [none]

/-- A refusal is a refusal of the bound: `check` errs exactly when the bound fails. -/
theorem check_error_iff {kind : ResourceKind} (scope : Scope kind) (operations : List Operation)
    (account : AccountId) :
    (∃ refusal, check scope operations account = .error refusal) ↔
      ¬ ValueBound scope operations account := by
  rw [← check_ok_iff]
  cases check scope operations account with
  | ok done => cases done; simp
  | error refusal => simp

/-! ## What an absent bound means, and narrowing -/

/-- **An absent bound bounds nothing.** A scope that names no field set and sets no bound
covers every debit: root grants, and the delegations issued without `maxDelta`. -/
theorem valueBound_of_unrestricted {kind : ResourceKind} (scope : Scope kind)
    (operations : List Operation) (account : AccountId)
    (everyField : scope.fields = none) (noBound : scope.maxDelta = ∅) :
    ValueBound scope operations account := by
  intro field _
  refine ⟨?_, ?_⟩
  · rw [everyField]
    exact trivial
  · intro bound member
    rw [noBound] at member
    exact absurd member (Finset.notMem_empty bound)

/-- **A bound survives delegation.** What a child scope covers, its parent covers; so a
child cannot move more than any ancestor's bound allows. -/
theorem valueBound_of_narrows {kind : ResourceKind} {child parent : Scope kind}
    {parentage : Parentage} (narrows : child.Narrows parent parentage)
    {operations : List Operation} {account : AccountId}
    (bounded : ValueBound child operations account) : ValueBound parent operations account :=
  narrows_fields_monotone narrows bounded

/-- Operations that never debit `account` are within every scope. -/
theorem valueBound_of_no_debit {kind : ResourceKind} (scope : Scope kind)
    (operations : List Operation) (account : AccountId)
    (none : debits operations account = []) : ValueBound scope operations account := by
  intro field touched
  obtain ⟨asset, member, rfl⟩ := Finset.mem_image.mp touched
  have listed : asset ∈ debitAssetList operations account := List.mem_toFinset.mp member
  unfold debitAssetList at listed
  rw [none] at listed
  cases listed

/-- A bound that admits a fee admits a smaller fee of the same asset from the same payer. -/
theorem valueBound_fee_mono {kind : ResourceKind} (scope : Scope kind)
    (payer collector : AccountId) (asset : AssetId) {less more : Nat} (le : less ≤ more)
    (bounded : ValueBound scope [.fee payer collector asset more] payer) :
    ValueBound scope [.fee payer collector asset less] payer := by
  rw [valueBound_iff] at bounded ⊢
  intro debited member
  have same : debited = asset := by
    simp [debitAssets, debitAssetList, debits, Operation.posting] at member
    first | exact member | exact member.symm
  rw [same]
  obtain ⟨named, within⟩ := bounded asset
    (by simp [debitAssets, debitAssetList, debits, Operation.posting])
  refine ⟨named, fun bound listed => ?_⟩
  have limit := within bound listed
  simp [grossDebit, debits, Operation.posting] at limit ⊢
  omega

/-! ## The statement for one admitted batch -/

/-- **Every debit of the batch is within its presented capability's value bound.**
`presented account` is the scope of the capability the receiver admitted for `account`'s
debit (`none`: no capability was presented for it). -/
def BatchBounded {kind : ResourceKind} (presented : AccountId → Option (Scope kind))
    (operations : List Operation) : Prop :=
  ∀ operation ∈ operations, ∃ scope, presented operation.posting.source = some scope ∧
    ValueBound scope operations operation.posting.source

theorem mem_debitAssets_of_mem {operations : List Operation} {operation : Operation}
    (member : operation ∈ operations) :
    operation.posting.asset ∈ debitAssets operations operation.posting.source := by
  unfold debitAssets debitAssetList debits
  rw [List.mem_toFinset, List.mem_map]
  refine ⟨operation.posting, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨List.mem_map.mpr ⟨operation, member, rfl⟩, by simp⟩

/-- Under `BatchBounded`, the balance each operation debits is named by the presented scope,
and the batch's gross debit of that account in that asset is within every bound it sets. -/
theorem batchBounded_gross {kind : ResourceKind} {presented : AccountId → Option (Scope kind)}
    {operations : List Operation} (bounded : BatchBounded presented operations)
    {operation : Operation} (member : operation ∈ operations) :
    ∃ scope, presented operation.posting.source = some scope ∧
      CellField.NamedBy scope.fields (.balance operation.posting.asset) ∧
        ∀ bound, (CellField.balance operation.posting.asset, bound) ∈ scope.maxDelta →
          grossDebit operations operation.posting.source operation.posting.asset ≤ bound := by
  obtain ⟨scope, named, covered⟩ := bounded operation member
  exact ⟨scope, named,
    (valueBound_iff scope operations operation.posting.source).mp covered _
      (mem_debitAssets_of_mem member)⟩

/-! ## Delegated capabilities must set the bound

`ValueBound` reads an absent bound as no bound. That is right for a root capability, whose
holder owns the account. A delegated capability (one with a parent in its lineage) must set a
`maxDelta` bound on every balance it debits: an omitted limit must not expose the delegator's
whole balance. Only the lineage (`parent = none`) gives the root exemption; holding an owner
grant does not.

The bound is a limit on ONE batch (one admitted turn), not a cumulative allowance: repeated
turns, each within the bound, can still move more than the bound in total. -/

/-- The scope sets some `maxDelta` bound on the balance of `asset`. -/
def HasBound {kind : ResourceKind} (scope : Scope kind) (asset : AssetId) : Prop :=
  ∃ entry ∈ scope.maxDelta, entry.1 = CellField.balance asset

instance {kind : ResourceKind} (scope : Scope kind) (asset : AssetId) :
    Decidable (HasBound scope asset) := by
  unfold HasBound
  infer_instance

theorem hasBound_iff {kind : ResourceKind} (scope : Scope kind) (asset : AssetId) :
    HasBound scope asset ↔ ∃ bound, (CellField.balance asset, bound) ∈ scope.maxDelta := by
  constructor
  · rintro ⟨⟨field, bound⟩, member, same⟩
    change field = CellField.balance asset at same
    subst same
    exact ⟨bound, member⟩
  · rintro ⟨bound, member⟩
    exact ⟨_, member, rfl⟩

/-- A delegated capability sets a bound on every balance the operations debit from the
account. A root capability (`parent = none`) owes none. -/
def BoundsSet {kind : ResourceKind} (cap : Capability kind) (operations : List Operation)
    (account : AccountId) : Prop :=
  cap.parent ≠ none → ∀ asset ∈ debitAssets operations account,
    ∃ bound, (CellField.balance asset, bound) ∈ cap.scope.maxDelta

/-- **The strict value bound**, the condition every debiting receiver adds to its existing
authorization of an account debit (fees included): the scope names every debited balance and
every bound it sets holds for the gross debit, and a delegated capability sets a bound on
every debited balance. -/
def StrictBound {kind : ResourceKind} (cap : Capability kind) (operations : List Operation)
    (account : AccountId) : Prop :=
  ValueBound cap.scope operations account ∧ BoundsSet cap operations account

/-- The first debited asset, in posting order, on which a delegated capability sets no bound. -/
def missingBound {kind : ResourceKind} (cap : Capability kind) (operations : List Operation)
    (account : AccountId) : Option AssetId :=
  if cap.parent = none then none
  else (debitAssetList operations account).find? fun asset => !decide (HasBound cap.scope asset)

theorem missingBound_eq_none_iff {kind : ResourceKind} (cap : Capability kind)
    (operations : List Operation) (account : AccountId) :
    missingBound cap operations account = none ↔ BoundsSet cap operations account := by
  unfold missingBound BoundsSet
  by_cases root : cap.parent = none
  · rw [if_pos root]
    exact iff_of_true rfl (fun delegated => absurd root delegated)
  · rw [if_neg root, List.find?_eq_none]
    constructor
    · intro all _ asset member
      have listed : asset ∈ debitAssetList operations account := by
        simpa [debitAssets] using member
      have bound := all asset listed
      simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq, Bool.not_not] at bound
      exact (hasBound_iff _ _).mp (by simpa using bound)
    · intro all asset listed
      have bound := (hasBound_iff _ _).mpr
        (all root asset (by simpa [debitAssets] using listed))
      simp [bound]

/-- The strict check: the scope's own refusal first, then the missing bound, each by name. -/
def strictCheck {kind : ResourceKind} (cap : Capability kind) (operations : List Operation)
    (account : AccountId) : Except Refusal Unit :=
  match check cap.scope operations account with
  | .error refusal => .error refusal
  | .ok () =>
      match missingBound cap operations account with
      | some asset => .error (.missingBalanceBound asset)
      | none => .ok ()

/-- **The strict check decides the strict bound.** -/
theorem strictCheck_ok_iff {kind : ResourceKind} (cap : Capability kind)
    (operations : List Operation) (account : AccountId) :
    strictCheck cap operations account = .ok () ↔ StrictBound cap operations account := by
  unfold strictCheck StrictBound
  rw [← check_ok_iff, ← missingBound_eq_none_iff]
  cases check cap.scope operations account with
  | error refusal => simp
  | ok done =>
    cases done
    cases missingBound cap operations account <;> simp

instance {kind : ResourceKind} (cap : Capability kind) (operations : List Operation)
    (account : AccountId) : Decidable (StrictBound cap operations account) :=
  decidable_of_iff _ (strictCheck_ok_iff cap operations account)

/-- A refusal is a refusal of the strict bound. -/
theorem strictCheck_error_iff {kind : ResourceKind} (cap : Capability kind)
    (operations : List Operation) (account : AccountId) :
    (∃ refusal, strictCheck cap operations account = .error refusal) ↔
      ¬ StrictBound cap operations account := by
  rw [← strictCheck_ok_iff]
  cases strictCheck cap operations account with
  | ok done => cases done; simp
  | error refusal => simp

/-- A root capability's strict bound is its scope's bound: absent stays unbounded. -/
theorem strictBound_root {kind : ResourceKind} (cap : Capability kind)
    (operations : List Operation) (account : AccountId) (root : cap.parent = none) :
    StrictBound cap operations account ↔ ValueBound cap.scope operations account :=
  ⟨fun strict => strict.1, fun bounded => ⟨bounded, fun delegated => absurd root delegated⟩⟩

/-- **A delegated capability's debit is bounded by a number it wrote.** Under the strict
bound, each debited balance carries a bound and the gross debit is within it. -/
theorem StrictBound.delegated_gross {kind : ResourceKind} {cap : Capability kind}
    {operations : List Operation} {account : AccountId}
    (strict : StrictBound cap operations account) (delegated : cap.parent ≠ none)
    {asset : AssetId} (member : asset ∈ debitAssets operations account) :
    ∃ bound, (CellField.balance asset, bound) ∈ cap.scope.maxDelta ∧
      grossDebit operations account asset ≤ bound := by
  obtain ⟨bound, listed⟩ := strict.2 delegated asset member
  exact ⟨bound, listed,
    ((valueBound_iff cap.scope operations account).mp strict.1 asset member).2 bound listed⟩

/-! ## The footprint form: a receiver that judges a leg by its `Footprint` -/

/-- A scope sets a bound on `field` when it is a balance; other fields owe none. -/
def BalanceBounded {kind : ResourceKind} (scope : Scope kind) : CellField → Prop
  | .balance asset => HasBound scope asset
  | _ => True

instance {kind : ResourceKind} (scope : Scope kind) (field : CellField) :
    Decidable (BalanceBounded scope field) := by
  cases field <;> unfold BalanceBounded <;> infer_instance

/-- **The missing-bound half of the strict bound, on a footprint.** A delegated capability
sets a bound on every balance the footprint lowers. A root capability owes none; a balance the
footprint raises or leaves owes none. -/
def DebitsBounded {kind : ResourceKind} (cap : Capability kind) (footprint : Footprint) : Prop :=
  cap.parent ≠ none → ∀ field ∈ footprint.touched, footprint.delta field < 0 →
    BalanceBounded cap.scope field

instance {kind : ResourceKind} (cap : Capability kind) (footprint : Footprint) :
    Decidable (DebitsBounded cap footprint) := by
  unfold DebitsBounded
  infer_instance

theorem debitsBounded_root {kind : ResourceKind} (cap : Capability kind) (footprint : Footprint)
    (root : cap.parent = none) : DebitsBounded cap footprint :=
  fun delegated => absurd root delegated

/-- The operation form implies the footprint form on the gross-debit footprint. -/
theorem BoundsSet.debitsBounded {kind : ResourceKind} {cap : Capability kind}
    {operations : List Operation} {account : AccountId}
    (set : BoundsSet cap operations account) :
    DebitsBounded cap (debitFootprint operations account) := by
  intro delegated field touched _
  obtain ⟨asset, member, rfl⟩ := Finset.mem_image.mp touched
  exact (hasBound_iff _ _).mpr (set delegated asset member)

/-- They agree when every debited balance is debited a positive amount. -/
theorem debitsBounded_iff_boundsSet {kind : ResourceKind} (cap : Capability kind)
    (operations : List Operation) (account : AccountId)
    (positive : ∀ asset ∈ debitAssets operations account,
      0 < grossDebit operations account asset) :
    DebitsBounded cap (debitFootprint operations account) ↔
      BoundsSet cap operations account := by
  refine ⟨fun bounded delegated asset member => ?_, BoundsSet.debitsBounded⟩
  have lowered : (debitFootprint operations account).delta (.balance asset) < 0 := by
    have pos := positive asset member
    change -(Int.ofNat (grossDebit operations account asset)) < 0
    simp only [Int.ofNat_eq_coe]
    omega
  exact (hasBound_iff _ _).mp
    (bounded delegated (.balance asset) (Finset.mem_image_of_mem _ member) lowered)

/-! ## The receiver's form: the capability a debit was authorized under -/

/-- **The presented capability bounds the debit.** `capability` is what the receiver's
authorization evidence holds for the debit of `account` (the capability and its commitment;
`none`: the debit was authorized under no capability). -/
def Presented {kind : ResourceKind} {D : Type} (capability : Option (Capability kind × D))
    (operations : List Operation) (account : AccountId) : Prop :=
  ∃ cap commitment, capability = some (cap, commitment) ∧
    StrictBound cap operations account

/-- The decision of `Presented`. `error none`: no capability; `error (some refusal)`: the
capability does not bound the debit, by name. -/
def presentedCheck {kind : ResourceKind} {D : Type} (capability : Option (Capability kind × D))
    (operations : List Operation) (account : AccountId) : Except (Option Refusal) Unit :=
  match capability with
  | none => .error none
  | some (cap, _) =>
      match strictCheck cap operations account with
      | .ok () => .ok ()
      | .error refusal => .error (some refusal)

theorem presentedCheck_ok_iff {kind : ResourceKind} {D : Type}
    (capability : Option (Capability kind × D)) (operations : List Operation)
    (account : AccountId) :
    presentedCheck capability operations account = .ok () ↔
      Presented capability operations account := by
  unfold presentedCheck Presented
  rcases capability with _ | ⟨cap, commitment⟩
  · simp
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro ok
      refine ⟨cap, commitment, ⟨rfl, rfl⟩, ?_⟩
      split at ok
      next checked => exact (strictCheck_ok_iff _ _ _).mp checked
      next => cases ok
    · rintro ⟨_, _, ⟨rfl, rfl⟩, bounded⟩
      rw [(strictCheck_ok_iff _ _ _).mpr bounded]

instance {kind : ResourceKind} {D : Type} (capability : Option (Capability kind × D))
    (operations : List Operation) (account : AccountId) :
    Decidable (Presented capability operations account) :=
  decidable_of_iff _ (presentedCheck_ok_iff capability operations account)

/-- Teeth: a presented capability that fails the strict bound is refused, by name. -/
theorem presentedCheck_refuses {kind : ResourceKind} {D : Type} (cap : Capability kind)
    (commitment : D) (operations : List Operation) (account : AccountId)
    (unbounded : ¬ StrictBound cap operations account) :
    ∃ refusal, presentedCheck (some (cap, commitment)) operations account =
      .error (some refusal) := by
  obtain ⟨refusal, refused⟩ := (strictCheck_error_iff _ _ _).mpr unbounded
  exact ⟨refusal, by simp only [presentedCheck, refused]⟩

theorem Presented.fee_mono {kind : ResourceKind} {D : Type}
    {capability : Option (Capability kind × D)} {payer collector : AccountId} {asset : AssetId}
    {less more : Nat} (le : less ≤ more)
    (presented : Presented capability [.fee payer collector asset more] payer) :
    Presented capability [.fee payer collector asset less] payer := by
  obtain ⟨cap, commitment, named, bounded, set⟩ := presented
  exact ⟨cap, commitment, named, valueBound_fee_mono cap.scope payer collector asset le bounded,
    fun delegated debited member => set delegated debited (by
      simpa [debitAssets, debitAssetList, debits, Operation.posting] using member)⟩

/-- In plain terms: under `Presented`, every balance the operations debit from the account is
named, and its gross debit is within every bound the capability sets on it. -/
theorem Presented.gross {kind : ResourceKind} {D : Type}
    {capability : Option (Capability kind × D)} {operations : List Operation}
    {account : AccountId} (presented : Presented capability operations account) :
    ∃ cap commitment, capability = some (cap, commitment) ∧
      ∀ asset ∈ debitAssets operations account,
        CellField.NamedBy cap.scope.fields (.balance asset) ∧
          ∀ bound, (CellField.balance asset, bound) ∈ cap.scope.maxDelta →
            grossDebit operations account asset ≤ bound := by
  obtain ⟨cap, commitment, named, bounded⟩ := presented
  exact ⟨cap, commitment, named, (valueBound_iff cap.scope operations account).mp bounded.1⟩

/-- Under `Presented`, a delegated capability wrote a bound on every debited balance and the
gross debit is within it. -/
theorem Presented.delegated_gross {kind : ResourceKind} {D : Type}
    {capability : Option (Capability kind × D)} {operations : List Operation}
    {account : AccountId} (presented : Presented capability operations account) :
    ∃ cap commitment, capability = some (cap, commitment) ∧
      (cap.parent ≠ none → ∀ asset ∈ debitAssets operations account,
        ∃ bound, (CellField.balance asset, bound) ∈ cap.scope.maxDelta ∧
          grossDebit operations account asset ≤ bound) := by
  obtain ⟨cap, commitment, named, strict⟩ := presented
  exact ⟨cap, commitment, named, fun delegated _ member => strict.delegated_gross delegated member⟩

/-! ## Witnesses -/

namespace Witness

/-- Account 7 pays; asset 0 is the credit asset. -/
def payer : AccountId := 7
def other : AccountId := 9
def credit : AssetId := 0
def gold : AssetId := 1

/-- A delegated spend scope bounded at 5 of `credit` a turn, naming only that balance. -/
def bounded : Scope .account where
  targets := .explicit {⟨payer⟩}
  verbs := {.transfer}
  maxCost := 3
  fields := some {.balance credit}
  maxDelta := {(.balance credit, 5)}

/-- A root grant's scope: every field, no bound. -/
def root : Scope .account where
  targets := .explicit {⟨payer⟩}
  verbs := {.transfer}
  maxCost := 100000

def within : List Operation := [.transfer payer other credit 5]
def over : List Operation := [.transfer payer other credit 6]
def split : List Operation := [.transfer payer other credit 3, .transfer payer other credit 3]
def offset : List Operation := [.transfer other payer credit 10, .transfer payer other credit 6]
def otherAsset : List Operation := [.transfer payer other gold 1]
def feeOnly : List Operation := [.fee payer other credit 3]
def large : List Operation := [.transfer payer other credit 1000000]

/-- Premise inhabitation: the witness batch does debit the payer, in the bounded asset. -/
theorem premise_inhabited :
    debits within payer = [⟨payer, other, credit, 5⟩] ∧ grossDebit within payer credit = 5 := by
  decide

/-- Satisfiable: a debit at the bound is admitted. -/
theorem within_admitted : check bounded within payer = .ok () := by decide

/-- Teeth: one past the bound is refused by name. -/
theorem over_refused : check bounded over payer = .error (.maxDeltaExceeded credit 6) := by
  decide

/-- Teeth: the bound is on the gross debit, so two debits under it together exceed it. -/
theorem split_refused : check bounded split payer = .error (.maxDeltaExceeded credit 6) := by
  decide

/-- Teeth: a credit in the same batch does not offset the debit. -/
theorem credit_does_not_offset :
    check bounded offset payer = .error (.maxDeltaExceeded credit 6) := by
  decide

/-- Teeth: a balance the scope does not name is refused by name, whatever the amount. -/
theorem unnamed_refused : check bounded otherAsset payer = .error (.fieldNotNamed gold) := by
  decide

/-- A fee is a debit like any other: within the bound it passes. -/
theorem fee_within : check bounded feeOnly payer = .ok () := by decide

/-- An absent bound bounds nothing: the root scope covers a debit of any size. -/
theorem root_unbounded : ValueBound root large payer :=
  valueBound_of_unrestricted root large payer rfl rfl

/-- The same large debit is refused under the bounded scope. -/
theorem large_refused :
    check bounded large payer = .error (.maxDeltaExceeded credit 1000000) := by
  decide

/-- Another account's debit is not this capability's concern. -/
theorem other_account_unjudged : check bounded large other = .ok () := by decide

/-- A capability over the payer with the given lineage and scope. -/
def capability (parent : Option CapabilityId) (scope : Scope .account) : Capability .account where
  id := ⟨21⟩
  root := ⟨20⟩
  parent := parent
  issuer := ⟨7⟩
  holder := .subject ⟨4⟩
  scope := scope
  notBefore := 0
  notAfter := 100
  issuerEpoch := 0
  policyId := ⟨payer⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

/-- A scope that bounds the credit balance at zero. -/
def zero : Scope .account := { bounded with maxDelta := {(.balance credit, 0)} }

/-- Strict, satisfiable: a delegated capability with a bound, within it. -/
theorem delegated_within_admitted :
    strictCheck (capability (some ⟨20⟩) bounded) within payer = .ok () := by decide

/-- Strict, teeth: a delegated capability with no bound is refused for any positive debit,
however small, naming the balance. -/
theorem delegated_unbounded_refused :
    strictCheck (capability (some ⟨20⟩) root) feeOnly payer =
      .error (.missingBalanceBound credit) := by decide

/-- Footprint form, satisfiable: a delegated capability that bounds the lowered balance. -/
theorem footprint_bounded :
    DebitsBounded (capability (some ⟨20⟩) bounded) (debitFootprint within payer) := by decide

/-- Footprint form, teeth: a delegated capability with no bound on a lowered balance. -/
theorem footprint_unbounded_refused :
    ¬ DebitsBounded (capability (some ⟨20⟩) root) (debitFootprint feeOnly payer) := by decide

/-- Footprint form: the same footprint under a root capability owes no bound. -/
theorem footprint_root :
    DebitsBounded (capability none root) (debitFootprint feeOnly payer) := by decide

/-- Strict, teeth: a delegated capability bounded at zero cannot pay a positive fee. -/
theorem delegated_zero_cannot_pay_fee :
    strictCheck (capability (some ⟨20⟩) zero) feeOnly payer =
      .error (.maxDeltaExceeded credit 3) := by decide

/-- Strict: a root capability with no bound is admitted at any size. -/
theorem root_unbounded_admitted :
    strictCheck (capability none root) large payer = .ok () := by decide

/-- Strict: a delegated capability that debits nothing owes no bound. -/
theorem delegated_no_debit_admitted :
    strictCheck (capability (some ⟨20⟩) root) large other = .ok () := by decide

/-- Premise inhabitation: the refused delegated capability is delegated, and the batch it is
refused on debits the payer. -/
theorem strict_premise_inhabited :
    (capability (some ⟨20⟩) root).parent ≠ none ∧ grossDebit feeOnly payer credit = 3 := by
  decide

/-- The batch statement, satisfiable: the payer presents the bounded scope. -/
theorem batch_bounded :
    BatchBounded (fun account => if account = payer then some bounded else none) within := by
  intro operation member
  have same : operation = .transfer payer other credit 5 := by simpa [within] using member
  subst same
  exact ⟨bounded, by decide, (check_ok_iff _ _ _).mp within_admitted⟩

/-- The batch statement, teeth: with no capability presented for the payer it fails. -/
theorem batch_unpresented_fails :
    ¬ BatchBounded (kind := .account) (fun _ => none) within := by
  intro bounded
  obtain ⟨scope, named, _⟩ := bounded (.transfer payer other credit 5) (by simp [within])
  cases named

end Witness

#assert_axioms valueBound_iff
#assert_axioms check_ok_iff
#assert_axioms check_error_iff
#assert_axioms valueBound_of_unrestricted
#assert_axioms valueBound_of_narrows
#assert_axioms batchBounded_gross
#assert_axioms Witness.within_admitted
#assert_axioms Witness.over_refused
#assert_axioms Witness.split_refused
#assert_axioms Witness.credit_does_not_offset
#assert_axioms Witness.unnamed_refused
#assert_axioms Witness.root_unbounded
#assert_axioms Witness.batch_bounded
#assert_axioms Witness.delegated_within_admitted Witness.delegated_unbounded_refused
#assert_axioms Witness.delegated_zero_cannot_pay_fee Witness.root_unbounded_admitted
#assert_axioms strictCheck_ok_iff missingBound_eq_none_iff presentedCheck_ok_iff

end Minidregg.Theory.CapabilityValueBound
