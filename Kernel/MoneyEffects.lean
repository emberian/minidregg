/-
# `Kernel/MoneyEffects.lean` — the two money consents, each ONE declaration

* `computeFundingEffect` (code 6, JSON `computeFunding`): an account's consent to the debit that
  pays for the command's compute. The operation names the asset, the credits, the payer balance
  and the Book root it expects.
* `moneyConsentEffect` (code 8, JSON `moneyConsent`): an account's consent to its positions in a
  canonical Book batch, with an optional compute funding.

Neither writes its target: the account's cell is left as loaded (`unchanging`), the root is
pinned, and the transaction enters the target as a read guard. What they do is on the shared
Book, which is the transaction's (`prepareCompute`, `prepareMoney` read the signed operations);
so neither states a member patch (`member = none`: thin consent refuses them by name), neither
has a rotate, and a run can claim nothing of a money consent and the empty write list of the
validated funding leg only. Their one refusal is a target that carries audience fields.

The funding's footprint is its declaration's (`Effect.footprint`): the debit of its credits on
the balance of its asset. A money consent's own footprint is empty; its monetary footprint is
the admitted batch's (`monetaryFootprint?`).
-/
module

public import Kernel.ResourceEffect
public import Kernel.ResourceGrammarJson
public import Kernel.ResourceMoneyWire
public import Kernel.ResourceObservationAdmission

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

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- The explicit consent to a source-derived Book burn that pays for compute. Payer and
capability are the containing signed account target, not duplicated here. -/
abbrev ComputeFunding := ResourceMoneyWire.FundingConsent
abbrev computeFundingStream := ResourceMoneyWire.fundingStream
abbrev MoneyConsent := ResourceMoneyWire.Consent

/-- The one refusal of a money consent's own semantics. -/
inductive MoneyRefusal where
  /-- The target carries an audience epoch or roster: an account has no audience. -/
  | audienceFields
  deriving DecidableEq, Repr

def MoneyRefusal.name : MoneyRefusal → String
  | .audienceFields => "audienceFields"

/-- A money consent leaves its target as loaded; it refuses a target with audience fields. -/
def moneySem {O : Type} (ctx : EffectCtx) (_ : O) (_ : Store EffectDeclaration.effectLayout) :
    Except MoneyRefusal (Patch EffectDeclaration.effectLayout) :=
  if ctx.audienceEpoch.isSome || ctx.audienceRoster.isSome then .error .audienceFields else .ok []

/-- An admitted money consent emits nothing and its target carries no audience field. -/
theorem moneySem_ok {O : Type} {ctx : EffectCtx} {op : O}
    {store : Store EffectDeclaration.effectLayout} {ps : Patch EffectDeclaration.effectLayout}
    (ok : moneySem ctx op store = .ok ps) :
    ps = [] ∧ ctx.audienceEpoch = none ∧ ctx.audienceRoster = none := by
  unfold moneySem at ok
  split at ok
  · cases ok
  · rename_i plain
    refine ⟨(Except.ok.inj ok).symm, ?_, ?_⟩
    · cases epoch : ctx.audienceEpoch with
      | none => rfl
      | some _ => simp [epoch] at plain
    · cases roster : ctx.audienceRoster with
      | none => rfl
      | some _ => simp [roster] at plain

/-- The explicit consent's numeric view. `prepareCompute` binds these exact payer balance, Book
root and credits to the loaded Book before an accepted invocation can use them; no arbitrary
balance mutation is installed in account metadata. -/
def fundingProject (funding : ComputeFunding) : List (String × Int) :=
  [("compute/charge", 1),
   ("compute/asset", Int.ofNat funding.asset),
   ("compute/credits", Int.ofNat funding.credits),
   ("compute/payer/before", funding.expectedPayerBalance),
   ("compute/payer/after", funding.expectedPayerBalance - Int.ofNat funding.credits)]

theorem fundingProject_unjoint (funding : ComputeFunding) :
    JointSlots.Unjoint (fundingProject funding) := by
  intro p hp
  simp only [fundingProject, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- A money consent's numeric view: that it consents, to how many positions, and its funding's. -/
def consentProject (consent : MoneyConsent) : List (String × Int) :=
  [("money/consent", 1), ("money/positions", Int.ofNat consent.positions.length)] ++
    (consent.funding.map fundingProject).getD []

theorem consentProject_unjoint (consent : MoneyConsent) :
    JointSlots.Unjoint (consentProject consent) := by
  apply JointSlots.unjoint_append
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> decide
  · cases funding : consent.funding with
    | none => intro p hp; cases hp
    | some supplied => exact fundingProject_unjoint supplied

/-- **A money consent's declaration**, over its operation type, its codec and its view: an
account's declared cell at schema version 1; the root is pinned; no rotate, an empty frame; the
authorization is the account's ordinary write. -/
def moneySpec {O : Type} (opStream : StreamCodec O) (view : O → List (String × Int)) :
    Revival.EffectSpec EffectCtx (Revival.storeSubstrate EffectDeclaration.effectLayout) O
      MoneyRefusal where
  opStream := opStream
  refusalName := MoneyRefusal.name
  accepts := fun kind => kind == .account
  version := 1
  sem := moneySem
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := fun _ => .body
  amount := fun _ _ => 0
  frame := fun _ => ∅
  verb := fun kind _ => DeclaredResourceScalar.ordinaryVerb kind
  view := fun _ op _ _ => view op

theorem moneySpec_emitted {O : Type} {opStream : StreamCodec O} {view : O → List (String × Int)}
    {ctx : EffectCtx} {op : O} {store : Store EffectDeclaration.effectLayout}
    {ps : Patch EffectDeclaration.effectLayout}
    (emitted : (moneySpec opStream view).emitted ctx op store = .ok ps) : ps = [] := by
  unfold Revival.EffectSpec.emitted at emitted
  cases sem : moneySem ctx op store with
  | error reason =>
      rw [show (moneySpec opStream view).sem ctx op store = moneySem ctx op store from rfl, sem]
        at emitted
      cases emitted
  | ok descriptor =>
      rw [show (moneySpec opStream view).sem ctx op store = moneySem ctx op store from rfl, sem]
        at emitted
      have empty := (moneySem_ok sem).1
      subst empty
      exact (Except.ok.inj emitted).symm

theorem moneySpec_complete {O : Type} (opStream : StreamCodec O)
    (view : O → List (String × Int)) : (moneySpec opStream view).Complete := by
  intro ctx op store ps ok
  have empty : ps = [] := (moneySem_ok (show moneySem ctx op store = .ok ps from ok)).1
  subst empty
  exact ⟨fun loc member => absurd member (Finset.notMem_empty loc), rfl⟩

/-! ## The JSON faces -/

def moneyOperationJson : CanonicalResourceKernel.Operation → Lean.Json
  | .transfer source destination asset amount => .mkObj
      [("type", .str "transfer"), ("source", EffectJson.decimal source), ("destination", EffectJson.decimal destination),
       ("asset", EffectJson.decimal asset), ("amount", EffectJson.decimal amount)]
  | .fee source destination asset amount => .mkObj
      [("type", .str "fee"), ("source", EffectJson.decimal source), ("destination", EffectJson.decimal destination),
       ("asset", EffectJson.decimal asset), ("amount", EffectJson.decimal amount)]
  | .mint asset destination amount => .mkObj
      [("type", .str "mint"), ("asset", EffectJson.decimal asset), ("destination", EffectJson.decimal destination),
       ("amount", EffectJson.decimal amount)]
  | .burn source asset amount => .mkObj
      [("type", .str "burn"), ("source", EffectJson.decimal source), ("asset", EffectJson.decimal asset),
       ("amount", EffectJson.decimal amount)]
  | .lease leaseId holder lessor asset rate epochs startsAt => .mkObj
      [("type", .str "lease"), ("leaseId", EffectJson.decimal leaseId), ("holder", EffectJson.decimal holder),
       ("lessor", EffectJson.decimal lessor), ("asset", EffectJson.decimal asset), ("rate", EffectJson.decimal rate),
       ("epochs", EffectJson.decimal epochs), ("startsAt", EffectJson.decimal startsAt)]
  | .setFloor asset account floor => .mkObj
      [("type", .str "setFloor"), ("asset", EffectJson.decimal asset), ("account", EffectJson.decimal account),
       ("floor", EffectJson.decimal floor)]
  | .sweep holder commons asset permille epochs amount => .mkObj
      [("type", .str "sweep"), ("holder", EffectJson.decimal holder), ("commons", EffectJson.decimal commons),
       ("asset", EffectJson.decimal asset), ("permille", EffectJson.decimal permille), ("epochs", EffectJson.decimal epochs),
       ("amount", EffectJson.decimal amount)]

/-- A funding's fields, as an inbox shows them. -/
def fundingFieldsJson (funding : ComputeFunding) : List (String × Lean.Json) :=
  [("asset", EffectJson.decimal funding.asset), ("credits", EffectJson.decimal funding.credits),
   ("expectedPayerBalance", EffectJson.signedDecimal funding.expectedPayerBalance),
   ("expectedBookRoot", EffectJson.decimal funding.expectedBookRoot.value)]

/-- The JSON face: `{"type": "computeFunding", "asset", "credits", "expectedPayerBalance",
"expectedBookRoot"}`. -/
def fundingOfJson (path : String) (json : Lean.Json) : Except String ComputeFunding := do
  let obj ← EffectJson.exactObject path
    ["type", "asset", "credits", "expectedPayerBalance", "expectedBookRoot"] json
  pure ⟨← EffectJson.nat (path ++ ".asset") (← EffectJson.field path "asset" obj),
    ← EffectJson.nat (path ++ ".credits") (← EffectJson.field path "credits" obj),
    ← EffectJson.int (path ++ ".expectedPayerBalance")
      (← EffectJson.field path "expectedPayerBalance" obj),
    ⟨← EffectJson.nat (path ++ ".expectedBookRoot")
      (← EffectJson.field path "expectedBookRoot" obj)⟩⟩

/-- Complete typed declaration view. Values become authoritative only through canonical native
preparation, signatures, current law and joint admission. -/
def consentToJson (consent : MoneyConsent) : List (String × Lean.Json) :=
  [("batch", (consent.batch.map fun batch => .mkObj
      [("expectedBookRoot", EffectJson.decimal batch.expectedBookRoot.value),
       ("operations", .arr (batch.operations.toArray.map moneyOperationJson))]).getD .null),
   ("positions", .arr (consent.positions.toArray.map EffectJson.decimal)),
   ("funding", (consent.funding.map fun funding => .mkObj (fundingFieldsJson funding)).getD .null)]

/-- The JSON face: `{"type": "moneyConsent", "batch", "positions", "funding"}`, the request
grammar's batch and funding. -/
def consentOfJson (path : String) (json : Lean.Json) : Except String MoneyConsent := do
  let obj ← EffectJson.exactObject path ["type", "batch", "positions", "funding"] json
  pure ⟨← EffectJson.optional (path ++ ".batch") ResourceGrammarJson.moneyBatch
      (← EffectJson.field path "batch" obj),
    ← EffectJson.list (path ++ ".positions") EffectJson.nat (← EffectJson.field path "positions" obj),
    ← EffectJson.optional (path ++ ".funding") ResourceGrammarJson.moneyFunding
      (← EffectJson.field path "funding" obj)⟩

/-! ## The declarations, as the registry binds them -/

/-- **The compute funding consent, as the registry binds it** (code 6, JSON `computeFunding`). -/
def computeFundingEffect : Effect where
  name := "computeFunding"
  L := EffectDeclaration.effectLayout
  wire := DeclaredEffectCell.wire
  O := ComputeFunding
  R := MoneyRefusal
  decO := inferInstance
  spec := moneySpec computeFundingStream fundingProject
  pack := DeclaredResourceScalar.packDeclared
  unpack := unpackDeclared
  toJson := fundingFieldsJson
  ofJson := fundingOfJson
  display := fun funding =>
    [s!"funds compute with {funding.credits} credits of asset {funding.asset}; payer pre-balance {funding.expectedPayerBalance}, Book root {funding.expectedBookRoot.value}"]
  footprint := some fun funding _ _ =>
    ⟨if funding.credits = 0 then ∅ else {.balance funding.asset},
      fun field => if field = .balance funding.asset then -(Int.ofNat funding.credits) else 0⟩
  runWrites := some fun _ _ _ _ funded _ => if funded then some [] else none
  unchanging := true
  unchanging_silent := fun _ _ _ _ _ emitted => moneySpec_emitted emitted
  accounting := true
  authors := fun _ => false
  unpack_pack := unpackDeclared_pack
  pack_unpack := packDeclared_unpack
  observes_silent := fun _ _ _ _ _ emitted => moneySpec_emitted emitted
  complete := moneySpec_complete _ _
  view_unjoint := fun _ funding _ _ => fundingProject_unjoint funding

/-- **The money consent, as the registry binds it** (code 8, JSON `moneyConsent`). -/
def moneyConsentEffect : Effect where
  name := "moneyConsent"
  L := EffectDeclaration.effectLayout
  wire := DeclaredEffectCell.wire
  O := MoneyConsent
  R := MoneyRefusal
  decO := inferInstance
  spec := moneySpec ResourceMoneyWire.consentStream consentProject
  pack := DeclaredResourceScalar.packDeclared
  unpack := unpackDeclared
  toJson := consentToJson
  ofJson := consentOfJson
  display := fun consent =>
    [s!"canonical Book batch: {(consent.batch.map fun batch => batch.operations.length).getD 0} operations carried; {consent.positions.length} signed source positions; {(consent.funding.map fun funding => funding.credits).getD 0} compute credits"]
  footprint := some fun _ _ _ => ⟨∅, fun _ => 0⟩
  -- A program's field-write output cannot certify canonical money.
  runWrites := some fun _ _ _ _ _ _ => none
  unchanging := true
  unchanging_silent := fun _ _ _ _ _ emitted => moneySpec_emitted emitted
  authors := fun _ => false
  unpack_pack := unpackDeclared_pack
  pack_unpack := packDeclared_unpack
  observes_silent := fun _ _ _ _ _ emitted => moneySpec_emitted emitted
  complete := moneySpec_complete _ _
  view_unjoint := fun _ consent _ _ => consentProject_unjoint consent

/-- Neither money consent states a member patch: a member is never shown a post for a write to
the shared Book. -/
theorem computeFunding_member_unstated : computeFundingEffect.member = none := rfl
theorem moneyConsent_member_unstated : moneyConsentEffect.member = none := rfl

/-- Both pin their root. -/
theorem computeFunding_pinned (funding : ComputeFunding) :
    computeFundingEffect.spec.commutes funding = false := rfl
theorem moneyConsent_pinned (consent : MoneyConsent) :
    moneyConsentEffect.spec.commutes consent = false := rfl

end Minidregg.Kernel.DeclaredResourceController
