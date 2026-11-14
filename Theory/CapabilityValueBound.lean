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

## What an absent bound means

`maxDelta` is a set of bounds and the empty set bounds nothing; `fields = none` names every
field (`TypedAuthorization` §2a). So a capability that names no field set and carries no
`balance` bound is unbounded in value (`valueBound_of_unrestricted`). This holds for a root
capability and for a delegated one alike: a delegation narrows only what its author wrote
(`CellField.BoundsNarrow`: a child may add a bound, never drop one), so the grants the tree
issues today without `maxDelta` keep the reach they have. A delegator bounds value by writing
the bound; once written, no descendant can loosen it (`valueBound_of_narrows`).

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

/-! ## The receiver's form: the capability a debit was authorized under -/

/-- **The presented capability bounds the debit.** `capability` is what the receiver's
authorization evidence holds for the debit of `account` (the capability and its commitment;
`none`: the debit was authorized under no capability). -/
def Presented {kind : ResourceKind} {D : Type} (capability : Option (Capability kind × D))
    (operations : List Operation) (account : AccountId) : Prop :=
  ∃ cap commitment, capability = some (cap, commitment) ∧
    ValueBound cap.scope operations account

/-- The decision of `Presented`. `error none`: no capability; `error (some refusal)`: the
scope does not bound the debit, by name. -/
def presentedCheck {kind : ResourceKind} {D : Type} (capability : Option (Capability kind × D))
    (operations : List Operation) (account : AccountId) : Except (Option Refusal) Unit :=
  match capability with
  | none => .error none
  | some (cap, _) =>
      match check cap.scope operations account with
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
      next checked => exact (check_ok_iff _ _ _).mp checked
      next => cases ok
    · rintro ⟨_, _, ⟨rfl, rfl⟩, bounded⟩
      rw [(check_ok_iff _ _ _).mpr bounded]

instance {kind : ResourceKind} {D : Type} (capability : Option (Capability kind × D))
    (operations : List Operation) (account : AccountId) :
    Decidable (Presented capability operations account) :=
  decidable_of_iff _ (presentedCheck_ok_iff capability operations account)

/-- Teeth: a presented capability whose scope fails the bound is refused, by name. -/
theorem presentedCheck_refuses {kind : ResourceKind} {D : Type} (cap : Capability kind)
    (commitment : D) (operations : List Operation) (account : AccountId)
    (unbounded : ¬ ValueBound cap.scope operations account) :
    ∃ refusal, presentedCheck (some (cap, commitment)) operations account =
      .error (some refusal) := by
  obtain ⟨refusal, refused⟩ := (check_error_iff _ _ _).mpr unbounded
  exact ⟨refusal, by simp only [presentedCheck, refused]⟩

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
  exact ⟨cap, commitment, named, (valueBound_iff cap.scope operations account).mp bounded⟩

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

end Minidregg.Theory.CapabilityValueBound
